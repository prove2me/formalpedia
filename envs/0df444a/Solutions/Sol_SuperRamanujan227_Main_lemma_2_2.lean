-- Prove2me | solution 1 for SuperRamanujan227.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T00:31:17.822986+00:00
-- url     : https://prove2.me/submissions/db09f7e2-a839-4be3-8773-6ac5731d90e5

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra

open Polynomial Matrix Finset BigOperators Filter Topology

namespace SuperRamanujan227.Main

/-! ### Section 1: Real-rooted polynomials, `kthLargestRoot`, continuity, and convex-combination bound -/

section RealRootedTools

lemma realRooted_of_no_nonreal_root {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ z : ℂ, 0 < z.im → Polynomial.aeval z p ≠ 0) :
    RealRooted p := by
  refine ⟨hp, ?_⟩
  have hmap : (p.map (algebraMap ℝ ℂ)) ≠ 0 := by
    intro h0
    exact hp (Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective (by simpa using h0))
  have hsplit : (p.map (algebraMap ℝ ℂ)).Splits := IsAlgClosed.splits _
  have hcardC : (p.map (algebraMap ℝ ℂ)).roots.card = p.natDegree := by
    rw [← Polynomial.Splits.natDegree_eq_card_roots hsplit,
      Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
  have hall_real : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, z.im = 0 := by
    intro z hz
    have hroot : Polynomial.aeval z p = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hmap).mp hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hconj : Polynomial.aeval (starRingEnd ℂ z) p = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        have h1 : (p.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) = p.map (algebraMap ℝ ℂ) := by
          rw [Polynomial.map_map]
          congr 1
          ext r
          simp
        rw [← h1, Polynomial.eval_map_apply, show Polynomial.eval z (p.map (algebraMap ℝ ℂ)) = 0 from
          (Polynomial.mem_roots hmap).mp hz, map_zero]
      exact h (starRingEnd ℂ z) (by simp [hlt]) hconj
    · exact h z hgt hroot
  have hroots_eq : p.roots.map (algebraMap ℝ ℂ) = (p.map (algebraMap ℝ ℂ)).roots := by
    ext z
    by_cases hzim : z.im = 0
    · obtain ⟨r, rfl⟩ : ∃ r : ℝ, (algebraMap ℝ ℂ r) = z := ⟨z.re, Complex.ext rfl (by simp [hzim])⟩
      rw [Multiset.count_map_eq_count' (algebraMap ℝ ℂ) _ Complex.ofReal_injective,
        Polynomial.count_roots, Polynomial.count_roots]
      apply le_antisymm
      · rw [Polynomial.le_rootMultiplicity_iff hmap]
        have hdvd := Polynomial.pow_rootMultiplicity_dvd p r
        have := Polynomial.map_dvd (algebraMap ℝ ℂ) hdvd
        simpa [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using this
      · rw [Polynomial.le_rootMultiplicity_iff hp]
        have hdvd := Polynomial.pow_rootMultiplicity_dvd (p.map (algebraMap ℝ ℂ)) (algebraMap ℝ ℂ r)
        have h1 : ((X - C r) ^ Polynomial.rootMultiplicity (algebraMap ℝ ℂ r)
            (p.map (algebraMap ℝ ℂ))).map (algebraMap ℝ ℂ) ∣ p.map (algebraMap ℝ ℂ) := by
          simpa [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using hdvd
        exact (Polynomial.map_dvd_map (algebraMap ℝ ℂ) Complex.ofReal_injective
          ((Polynomial.monic_X_sub_C r).pow _)).mp h1
    · have h0 : Multiset.count z (p.map (algebraMap ℝ ℂ)).roots = 0 :=
        Multiset.count_eq_zero.mpr (fun hz => hzim (hall_real z hz))
      have h1 : Multiset.count z (p.roots.map (algebraMap ℝ ℂ)) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hz
        rcases Multiset.mem_map.mp hz with ⟨r, _, rfl⟩
        exact hzim (by simp)
      rw [h0, h1]
  rw [← Multiset.card_map (algebraMap ℝ ℂ), hroots_eq, hcardC]

lemma monic_eq_prod_roots_of_realRooted {p : ℝ[X]} (hm : p.Monic) (hr : RealRooted p) :
    p = (p.roots.map (fun r => X - C r)).prod := by
  have hsplit : p.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    exact hr.2
  have := hsplit.eq_prod_roots
  rw [hm.leadingCoeff, C_1, one_mul] at this
  exact this

/-- Cauchy's root bound for a monic real polynomial. -/
lemma abs_le_one_add_sum_coeff_of_isRoot {p : ℝ[X]} (hm : p.Monic) {r : ℝ}
    (hr : p.IsRoot r) :
    |r| ≤ 1 + ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
  by_cases h1 : |r| ≤ 1
  · have hnn : 0 ≤ ∑ j ∈ Finset.range p.natDegree, |p.coeff j| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  · push Not at h1
    have hpow : r ^ p.natDegree = -(∑ j ∈ Finset.range p.natDegree, p.coeff j * r ^ j) := by
      have heval : p.eval r = 0 := hr
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_mul] at heval
      linarith
    have habs : |r| ^ p.natDegree ≤ |r| ^ (p.natDegree - 1) * ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
      calc |r| ^ p.natDegree
          = |r ^ p.natDegree| := (abs_pow r p.natDegree).symm
        _ = |∑ j ∈ Finset.range p.natDegree, p.coeff j * r ^ j| := by rw [hpow, abs_neg]
        _ ≤ ∑ j ∈ Finset.range p.natDegree, |p.coeff j * r ^ j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ Finset.range p.natDegree, |p.coeff j| * |r| ^ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_pow]
        _ ≤ ∑ j ∈ Finset.range p.natDegree, |p.coeff j| * |r| ^ (p.natDegree - 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j ≤ p.natDegree - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_of_lt h1) hj') (abs_nonneg _)
        _ = |r| ^ (p.natDegree - 1) * ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hd : 1 ≤ p.natDegree := by
      by_contra hd0
      push Not at hd0
      have h0 : p.natDegree = 0 := Nat.lt_one_iff.mp hd0
      have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
      rw [hp1] at hr
      simp at hr
    have hpos : 0 < |r| ^ (p.natDegree - 1) := pow_pos (by linarith) _
    have hmul : |r| ^ (p.natDegree - 1) * |r| ≤ |r| ^ (p.natDegree - 1) *
        ∑ j ∈ Finset.range p.natDegree, |p.coeff j| := by
      rwa [← pow_succ, Nat.sub_add_cancel hd]
    have hle := le_of_mul_le_mul_left hmul hpos
    linarith

lemma sortedRoots_prod {m : ℕ} {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree = m)
    (hr : RealRooted p) :
    p = ∏ i : Fin m, (X - C ((p.roots.sort (· ≥ ·)).getD i.val 0)) := by
  have hlen : (p.roots.sort (· ≥ ·)).length = m := by
    rw [Multiset.length_sort, hr.2, hd]
  have h1 := monic_eq_prod_roots_of_realRooted hm hr
  have hcoe : (↑(p.roots.sort (· ≥ ·)) : Multiset ℝ) = p.roots := Multiset.sort_eq p.roots (· ≥ ·)
  conv_lhs => rw [h1, ← hcoe]
  rw [Multiset.map_coe, Multiset.prod_coe]
  -- List.prod of a list of length m equals Finset.prod over Fin m
  have hlist_prod : ∀ (l : List ℝ[X]), l.length = m →
      l.prod = ∏ i : Fin m, l.getD i.val 1 := by
    intro l hl
    rw [← List.prod_ofFn (f := fun i : Fin m => l.getD i.val 1)]
    congr 1
    apply List.ext_getElem (by simp [hl])
    intro k hk1 _
    simp [List.getD, List.getElem?_eq_getElem hk1]
  rw [hlist_prod _ (by simp [hlen])]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : i.val < (p.roots.sort (· ≥ ·)).length := hlen ▸ i.isLt
  have hi' : i.val < ((p.roots.sort (· ≥ ·)).map (fun r => X - C r)).length := by simpa using hi
  simp [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']

lemma prod_linear_realRooted {m : ℕ} (r : Fin m → ℝ) :
    RealRooted (∏ i : Fin m, (X - C (r i))) := by
  have hm : (∏ i : Fin m, (X - C (r i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  refine ⟨hm.ne_zero, ?_⟩
  rw [Polynomial.roots_prod _ _ hm.ne_zero]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.card_map]
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i))]
  simp

lemma list_eq_of_perm_of_pairwise_ge : ∀ {l₁ l₂ : List ℝ},
    l₁.Perm l₂ → l₁.Pairwise (· ≥ ·) → l₂.Pairwise (· ≥ ·) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => absurd h.length_eq (by simp)
  | _ :: _, [], h, _, _ => absurd h.length_eq (by simp)
  | a :: t₁, b :: t₂, hperm, hp₁, hp₂ => by
    rw [List.pairwise_cons] at hp₁ hp₂
    have hab : a = b := by
      have ha : a ∈ b :: t₂ := hperm.subset List.mem_cons_self
      have hb : b ∈ a :: t₁ := hperm.symm.subset List.mem_cons_self
      rcases List.mem_cons.mp ha with rfl | ha'
      · rfl
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exact le_antisymm (hp₂.1 a ha') (hp₁.1 b hb')
    subst hab
    congr 1
    exact list_eq_of_perm_of_pairwise_ge ((List.perm_cons a).mp hperm) hp₁.2 hp₂.2

lemma prod_linear_sortedRoots {m : ℕ} {r : Fin m → ℝ}
    (hanti : ∀ i j : Fin m, i ≤ j → r j ≤ r i) :
    ((∏ i : Fin m, (X - C (r i))).roots.sort (· ≥ ·)) = List.ofFn r := by
  have hm : (∏ i : Fin m, (X - C (r i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have hroots : (∏ i : Fin m, (X - C (r i))).roots = ↑(List.ofFn r) := by
    rw [Polynomial.roots_prod _ _ hm.ne_zero]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    have hfin : (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := rfl
    rw [hfin, Multiset.map_coe]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp
  rw [hroots]
  apply list_eq_of_perm_of_pairwise_ge
  · exact Multiset.coe_eq_coe.mp (Multiset.sort_eq (↑(List.ofFn r) : Multiset ℝ) (· ≥ ·))
  · exact Multiset.pairwise_sort _ (· ≥ ·)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn]
    exact hanti ⟨i, hi⟩ ⟨j, hj⟩ (le_of_lt hij)

lemma tendsto_coeff_prod_linear {m : ℕ} {r : ℕ → Fin m → ℝ} {r₀ : Fin m → ℝ}
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (nhds (r₀ i))) :
    ∀ j, Tendsto (fun n => (∏ i : Fin m, (X - C (r n i))).coeff j) atTop
      (nhds ((∏ i : Fin m, (X - C (r₀ i))).coeff j)) := by
  suffices ∀ s : Finset (Fin m), ∀ j,
      Tendsto (fun n => (∏ i ∈ s, (X - C (r n i))).coeff j) atTop
        (nhds ((∏ i ∈ s, (X - C (r₀ i))).coeff j)) from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro j
    simp only [Finset.prod_empty]
    exact tendsto_const_nhds
  | @insert a s ha ih =>
    intro j
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    refine tendsto_finsetSum _ fun kl _ => ?_
    refine Tendsto.mul ?_ (ih kl.2)
    by_cases hk : kl.1 = 0
    · simp only [hk, Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub]
      exact (hr a).neg
    · by_cases hk1 : kl.1 = 1
      · simp only [hk1, Polynomial.coeff_sub, Polynomial.coeff_X_one,
          Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero]
        exact tendsto_const_nhds
      · simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
          if_neg hk, if_neg (Ne.symm hk1), sub_zero]
        exact tendsto_const_nhds

/-- Closure of monic real-rooted polynomials of degree `m` AND continuity of `kthLargestRoot`. -/
lemma tendsto_realRooted_and_kthLargestRoot {m : ℕ} {p : ℕ → ℝ[X]} {p₀ : ℝ[X]}
    (hpm : ∀ n, (p n).Monic) (hpd : ∀ n, (p n).natDegree = m)
    (hpr : ∀ n, RealRooted (p n))
    (_hp0m : p₀.Monic) (_hp0d : p₀.natDegree = m)
    (htend : ∀ j, Tendsto (fun n => (p n).coeff j) atTop (nhds (p₀.coeff j))) :
    RealRooted p₀ ∧
      ∀ k, 1 ≤ k → k ≤ m →
        Tendsto (fun n => kthLargestRoot (p n) k) atTop (nhds (kthLargestRoot p₀ k)) := by
  let r : ℕ → Fin m → ℝ := fun n i => ((p n).roots.sort (· ≥ ·)).getD i.val 0
  have hr_anti : ∀ n (i j : Fin m), i ≤ j → r n j ≤ r n i := by
    intro n i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · have hlen : ((p n).roots.sort (· ≥ ·)).length = m := by
        rw [Multiset.length_sort, (hpr n).2, hpd n]
      have hpw := Multiset.pairwise_sort (p n).roots (· ≥ ·)
      rw [List.pairwise_iff_getElem] at hpw
      have hi : i.val < ((p n).roots.sort (· ≥ ·)).length := hlen ▸ i.isLt
      have hj : j.val < ((p n).roots.sort (· ≥ ·)).length := hlen ▸ j.isLt
      simpa only [r, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using
        hpw i.val j.val hi hj hlt
  have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n (i : Fin m), |r n i| ≤ M := by
    have hcbdd : ∀ j : Fin m, ∃ C : ℝ, ∀ n, |(p n).coeff j.val| ≤ C := by
      intro j
      obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (htend j.val)).subset_closedBall 0
      refine ⟨max C 0, fun n => ?_⟩
      have hmem : (p n).coeff j.val ∈ Metric.closedBall (0 : ℝ) C := hC ⟨n, rfl⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
      exact le_trans hmem (le_max_left _ _)
    choose C hC using hcbdd
    refine ⟨1 + ∑ j : Fin m, max (C j) 0, ?_, fun n i => ?_⟩
    · have : 0 ≤ ∑ j : Fin m, max (C j) 0 := Finset.sum_nonneg fun j _ => le_max_right _ _
      linarith
    · have hlen : ((p n).roots.sort (· ≥ ·)).length = m := by
        rw [Multiset.length_sort, (hpr n).2, hpd n]
      have hi : i.val < ((p n).roots.sort (· ≥ ·)).length := hlen ▸ i.isLt
      have hmem : r n i ∈ (p n).roots := by
        have h1 : r n i ∈ (p n).roots.sort (· ≥ ·) := by
          simp only [r, List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        exact (Multiset.mem_sort (· ≥ ·)).mp h1
      have hroot : (p n).IsRoot (r n i) := (Polynomial.mem_roots (hpr n).1).mp hmem
      have hbound := abs_le_one_add_sum_coeff_of_isRoot (hpm n) hroot
      rw [hpd n, ← Fin.sum_univ_eq_sum_range] at hbound
      calc |r n i| ≤ 1 + ∑ j : Fin m, |(p n).coeff j.val| := hbound
        _ ≤ 1 + ∑ j : Fin m, max (C j) 0 := by
          gcongr with j _
          exact le_trans (hC j n) (le_max_left _ _)
  obtain ⟨M, hM0, hM⟩ := hbdd
  let K : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-M) M)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hrK : ∀ n, r n ∈ K := fun n i _ => abs_le.mp (hM n i)
  have hsubseq : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ r₀ : Fin m → ℝ,
        Tendsto (fun n => r (φ (ψ n))) atTop (nhds r₀) ∧
        (∀ i j : Fin m, i ≤ j → r₀ j ≤ r₀ i) ∧
        p₀ = ∏ i : Fin m, (X - C (r₀ i)) := by
    intro φ hφ
    obtain ⟨r₀, _, ψ, hψ, hlim⟩ := hK.tendsto_subseq (fun n => hrK (φ n))
    have hlim' : Tendsto (fun n => r (φ (ψ n))) atTop (nhds r₀) := hlim
    refine ⟨ψ, hψ, r₀, hlim', ?_, ?_⟩
    · intro i j hij
      have hi : Tendsto (fun n => r (φ (ψ n)) i) atTop (nhds (r₀ i)) := (tendsto_pi_nhds.mp hlim') i
      have hj : Tendsto (fun n => r (φ (ψ n)) j) atTop (nhds (r₀ j)) := (tendsto_pi_nhds.mp hlim') j
      exact le_of_tendsto_of_tendsto hj hi (Eventually.of_forall fun n => hr_anti (φ (ψ n)) i j hij)
    · ext j
      have h1 : Tendsto (fun n => (p (φ (ψ n))).coeff j) atTop (nhds (p₀.coeff j)) :=
        (htend j).comp (hφ.comp hψ).tendsto_atTop
      have h2 : Tendsto (fun n => (p (φ (ψ n))).coeff j) atTop
          (nhds ((∏ i : Fin m, (X - C (r₀ i))).coeff j)) := by
        have heq : ∀ n, p (φ (ψ n)) = ∏ i : Fin m, (X - C (r (φ (ψ n)) i)) := fun n =>
          sortedRoots_prod (hpm _) (hpd _) (hpr _)
        simpa only [heq] using tendsto_coeff_prod_linear (tendsto_pi_nhds.mp hlim') j
      exact tendsto_nhds_unique h1 h2
  obtain ⟨ψ0, hψ0, rstar, hlim0, hanti0, hp0_eq⟩ := hsubseq id strictMono_id
  have hp0_rr : RealRooted p₀ := hp0_eq ▸ prod_linear_realRooted rstar
  have hrstar_eq : ∀ k (hk1 : 1 ≤ k) (hkm : k ≤ m),
      rstar ⟨k - 1, by omega⟩ = kthLargestRoot p₀ k := by
    intro k hk1 hkm
    have hlt : k - 1 < m := by omega
    simp only [kthLargestRoot, if_pos hk1, hp0_eq, prod_linear_sortedRoots hanti0]
    simp [hlt]
  refine ⟨hp0_rr, fun k hk1 hkm => ?_⟩
  have hgoal : Tendsto (fun n => r n ⟨k - 1, by omega⟩) atTop (nhds (rstar ⟨k - 1, by omega⟩)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ N : ℕ, ∃ n ≥ N, ε ≤ dist (r n ⟨k - 1, by omega⟩) (rstar ⟨k - 1, by omega⟩) := hnot
    let φ : ℕ → ℕ := Nat.rec (Classical.choose (hex 0)) (fun _ prev => Classical.choose (hex (prev + 1)))
    have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ fun n => by
      have hspec : φ n + 1 ≤ Classical.choose (hex (φ n + 1)) := (Classical.choose_spec (hex (φ n + 1))).1
      change φ n < Classical.choose (hex (φ n + 1))
      omega
    have hφ_dist : ∀ n, ε ≤ dist (r (φ n) ⟨k - 1, by omega⟩) (rstar ⟨k - 1, by omega⟩) := by
      intro n
      cases n with
      | zero => exact (Classical.choose_spec (hex 0)).2
      | succ n => exact (Classical.choose_spec (hex (φ n + 1))).2
    obtain ⟨ψ, hψ, r₀, hlim, hanti, hp0_eq'⟩ := hsubseq φ hφ_mono
    have hr0_eq : r₀ ⟨k - 1, by omega⟩ = rstar ⟨k - 1, by omega⟩ := by
      have h1 : List.ofFn r₀ = List.ofFn rstar := by
        rw [← prod_linear_sortedRoots hanti, ← prod_linear_sortedRoots hanti0, ← hp0_eq', ← hp0_eq]
      have h2 := congrArg (fun l => l.getD (k - 1) 0) h1
      have hlt : k - 1 < m := by omega
      simp [hlt] at h2
      exact h2
    have hlimk : Tendsto (fun n => r (φ (ψ n)) ⟨k - 1, by omega⟩) atTop (nhds (rstar ⟨k - 1, by omega⟩)) := by
      rw [← hr0_eq]
      exact (tendsto_pi_nhds.mp hlim) ⟨k - 1, by omega⟩
    rw [Metric.tendsto_atTop] at hlimk
    obtain ⟨N, hN⟩ := hlimk ε hε
    linarith [hN N le_rfl, hφ_dist (ψ N)]
  rw [← hrstar_eq k hk1 hkm]
  have heq_fn : (fun n => kthLargestRoot (p n) k) = (fun n => r n ⟨k - 1, by omega⟩) := by
    ext n
    simp [kthLargestRoot, if_pos hk1, r]
  rwa [heq_fn]

/-- 10-line IVT proof: if every convex combination of monic degree-`m` polynomials `f0, f1` is
real-rooted, then `min (α_k f0) (α_k f1) ≤ α_k (p f0 + (1-p) f1)`. -/
lemma kthLargestRoot_convex_le {m : ℕ} {f0 f1 : ℝ[X]}
    (hf0_m : f0.Monic) (hf0_d : f0.natDegree = m)
    (hf1_m : f1.Monic) (hf1_d : f1.natDegree = m)
    (hconv : ∀ q ∈ Set.Icc (0 : ℝ) 1, RealRooted (C q * f0 + C (1 - q) * f1))
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    min (kthLargestRoot f0 k) (kthLargestRoot f1 k) ≤
      kthLargestRoot (C p * f0 + C (1 - p) * f1) k := by
  let F : ℝ → ℝ[X] := fun q => C q * f0 + C (1 - q) * f1
  have hF_coeff : ∀ q j, (F q).coeff j = q * f0.coeff j + (1 - q) * f1.coeff j := by
    intro q j
    simp only [F, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  have hF_deg_le : ∀ q, (F q).natDegree ≤ m := by
    intro q
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    rw [hF_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hf0_d ▸ hj),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hf1_d ▸ hj)]
    ring
  have hF_coeff_m : ∀ q, (F q).coeff m = 1 := by
    intro q
    rw [hF_coeff, ← hf0_d, hf0_m.coeff_natDegree, hf0_d, ← hf1_d, hf1_m.coeff_natDegree]
    ring
  have hF_deg : ∀ q, (F q).natDegree = m := by
    intro q
    apply le_antisymm (hF_deg_le q)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [hF_coeff_m q]
    exact one_ne_zero
  have hF_monic : ∀ q, (F q).Monic := by
    intro q
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hF_deg q, hF_coeff_m q]
  let g : ℝ → ℝ := fun q => kthLargestRoot (F q) k
  have hg_cont : ContinuousOn g (Set.Icc 0 1) := by
    rw [Metric.continuousOn_iff]
    intro q hq ε hε
    by_contra hnot
    push Not at hnot
    have hex : ∀ n : ℕ, ∃ q' ∈ Set.Icc (0 : ℝ) 1,
        dist q' q < 1 / ((n : ℝ) + 1) ∧ ε ≤ dist (g q') (g q) := fun n =>
      hnot (1 / ((n : ℝ) + 1)) (by positivity)
    choose qs hqs_mem hqs_dist hqs_g using hex
    have hqs_tend : Tendsto qs atTop (nhds q) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
      refine ⟨N, fun n hn => lt_trans (hqs_dist n) ?_⟩
      rw [div_lt_iff₀ (by positivity)]
      have hN' : (1 : ℝ) / δ < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        linarith
      have := (div_lt_iff₀ hδ).mp hN'
      linarith
    have hcoeff_tend : ∀ j, Tendsto (fun n => (F (qs n)).coeff j) atTop (nhds ((F q).coeff j)) := by
      intro j
      simp only [hF_coeff]
      exact (hqs_tend.mul tendsto_const_nhds).add
        ((tendsto_const_nhds.sub hqs_tend).mul tendsto_const_nhds)
    have hlim := (tendsto_realRooted_and_kthLargestRoot
      (fun n => hF_monic (qs n)) (fun n => hF_deg (qs n)) (fun n => hconv (qs n) (hqs_mem n))
      (hF_monic q) (hF_deg q) hcoeff_tend).2 k hk1 hkm
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim ε hε
    linarith [hN N le_rfl, hqs_g N]
  have hg0 : g 0 = kthLargestRoot f1 k := by simp [g, F]
  have hg1 : g 1 = kthLargestRoot f0 k := by simp [g, F]
  change min (kthLargestRoot f0 k) (kthLargestRoot f1 k) ≤ g p
  rw [← hg1, ← hg0]
  by_contra hlt
  push Not at hlt
  obtain ⟨qstar, hqstar_mem, hqstar_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨0, by norm_num, by norm_num⟩ hg_cont
  have hmin_lt : g qstar < min (g 1) (g 0) := lt_of_le_of_lt (hqstar_min hp) hlt
  have hlt0 : g qstar < g 0 := lt_of_lt_of_le hmin_lt (min_le_right _ _)
  have hlt1 : g qstar < g 1 := lt_of_lt_of_le hmin_lt (min_le_left _ _)
  have hq0 : 0 < qstar := lt_of_le_of_ne hqstar_mem.1 (by rintro rfl; exact lt_irrefl _ hlt0)
  have hq1 : qstar < 1 := lt_of_le_of_ne hqstar_mem.2 (by rintro rfl; exact lt_irrefl _ hlt1)
  have hroot_all : ∀ y ∈ Set.Ioo (g qstar) (min (g 1) (g 0)), f0.eval y = 0 := by
    intro y hy
    have hcont1 : ContinuousOn g (Set.Icc 0 qstar) :=
      hg_cont.mono (Set.Icc_subset_Icc le_rfl hqstar_mem.2)
    have hcont2 : ContinuousOn g (Set.Icc qstar 1) :=
      hg_cont.mono (Set.Icc_subset_Icc hqstar_mem.1 le_rfl)
    obtain ⟨q1, hq1_mem, hq1_eq⟩ := intermediate_value_Icc' (le_of_lt hq0) hcont1
      ⟨le_of_lt hy.1, le_trans (le_of_lt hy.2) (min_le_right _ _)⟩
    obtain ⟨q2, hq2_mem, hq2_eq⟩ := intermediate_value_Icc (le_of_lt hq1) hcont2
      ⟨le_of_lt hy.1, le_trans (le_of_lt hy.2) (min_le_left _ _)⟩
    have hq1_lt : q1 < qstar := lt_of_le_of_ne hq1_mem.2 (by rintro rfl; linarith [hy.1])
    have hq2_gt : qstar < q2 := lt_of_le_of_ne hq2_mem.1 (by rintro rfl; linarith [hy.1])
    have hq12 : q1 ≠ q2 := ne_of_lt (lt_trans hq1_lt hq2_gt)
    have hisRoot : ∀ q ∈ Set.Icc (0 : ℝ) 1, (F q).eval (g q) = 0 := by
      intro q hq
      have hlen : ((F q).roots.sort (· ≥ ·)).length = m := by
        rw [Multiset.length_sort, (hconv q hq).2, hF_deg q]
      have hi : k - 1 < ((F q).roots.sort (· ≥ ·)).length := by omega
      have hmem : g q ∈ (F q).roots := by
        have h1 : g q ∈ (F q).roots.sort (· ≥ ·) := by
          simp only [g, kthLargestRoot, if_pos hk1, List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        exact (Multiset.mem_sort (· ≥ ·)).mp h1
      exact (Polynomial.mem_roots (hconv q hq).1).mp hmem
    have he1 : q1 * f0.eval y + (1 - q1) * f1.eval y = 0 := by
      have := hisRoot q1 ⟨hq1_mem.1, le_trans hq1_mem.2 hqstar_mem.2⟩
      rw [hq1_eq] at this
      simpa [F] using this
    have he2 : q2 * f0.eval y + (1 - q2) * f1.eval y = 0 := by
      have := hisRoot q2 ⟨le_trans hqstar_mem.1 hq2_mem.1, hq2_mem.2⟩
      rw [hq2_eq] at this
      simpa [F] using this
    have hsub : (q1 - q2) * (f0.eval y - f1.eval y) = 0 := by linarith
    have heq_f : f0.eval y = f1.eval y := by
      rcases mul_eq_zero.mp hsub with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hq12
      · exact sub_eq_zero.mp h0
    rw [heq_f] at he1
    linarith
  have hsub : Set.Ioo (g qstar) (min (g 1) (g 0)) ⊆ (f0.roots.toFinset : Set ℝ) := by
    intro y hy
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hf0_m.ne_zero,
      Polynomial.IsRoot]
    exact hroot_all y hy
  exact (Set.Ioo_infinite hmin_lt) (Set.Finite.subset (Finset.finite_toSet _) hsub)

end RealRootedTools

/-! ### Section 2: Siegel upper half-space real-stability and random-swap preservation -/

section SiegelStability

/-- `Z ∈ Sym_m(ℂ)` has positive definite imaginary part. -/
def IsSiegelPos {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Z.IsSymm ∧ ∀ v : Fin m → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (Z i j).im * v j

lemma isSiegelPos_re_symm {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : IsSiegelPos Z)
    (i j : Fin m) : (Z i j).re = (Z j i).re :=
  congrArg Complex.re (Matrix.IsSymm.apply hZ.1 i j).symm

lemma isSiegelPos_conj {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : IsSiegelPos Z)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ * P = 1) :
    IsSiegelPos ((P.map (algebraMap ℝ ℂ))ᵀ * Z * P.map (algebraMap ℝ ℂ)) := by
  set Pc : Matrix (Fin m) (Fin m) ℂ := P.map (algebraMap ℝ ℂ)
  refine ⟨?_, ?_⟩
  · change (Pcᵀ * Z * Pc)ᵀ = Pcᵀ * Z * Pc
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hZ.1.eq, Matrix.mul_assoc]
  · intro v hv
    have hPv : P *ᵥ v ≠ 0 := by
      intro h0
      have h1 : (Pᵀ * P) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      rw [hP, Matrix.one_mulVec] at h1
      exact hv h1
    have hpos := hZ.2 (P *ᵥ v) hPv
    have hPc : ∀ i j, ((Pcᵀ * Z * Pc) i j).im =
        ∑ k, ∑ l, P k i * (Z k l).im * P l j := by
      intro i j
      simp only [Pc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        Complex.coe_algebraMap, Complex.im_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Finset.sum_mul, Complex.im_sum, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    have heq : ∑ i, ∑ j, v i * ((Pcᵀ * Z * Pc) i j).im * v j =
        ∑ k, ∑ l, (P *ᵥ v) k * (Z k l).im * (P *ᵥ v) l := by
      simp_rw [hPc, Finset.mul_sum, Finset.sum_mul]
      calc ∑ i, ∑ j, ∑ k, ∑ l, v i * (P k i * (Z k l).im * P l j) * v j
          = ∑ k, ∑ l, ∑ i, ∑ j, (P k i * v i) * (Z k l).im * (P l j * v j) := by
            rw [Finset.sum_comm]
            trans ∑ j, ∑ k, ∑ l, ∑ i, v i * (P k i * (Z k l).im * P l j) * v j
            · refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_comm]
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ k, ∑ l, (P *ᵥ v) k * (Z k l).im * (P *ᵥ v) l := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
    rw [heq]
    exact hpos

lemma isSiegelPos_add_im_nonneg {m : ℕ} {Z W : Matrix (Fin m) (Fin m) ℂ}
    (hZ : IsSiegelPos Z) (hWsymm : W.IsSymm)
    (hW : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, v i * (W i j).im * v j) :
    IsSiegelPos (Z + W) := by
  refine ⟨hZ.1.add hWsymm, fun v hv => ?_⟩
  have heq : ∑ i, ∑ j, v i * ((Z + W) i j).im * v j =
      (∑ i, ∑ j, v i * (Z i j).im * v j) + (∑ i, ∑ j, v i * (W i j).im * v j) := by
    simp only [Matrix.add_apply, Complex.add_im, mul_add, add_mul, Finset.sum_add_distrib]
  rw [heq]
  linarith [hZ.2 v hv, hW v]

lemma det_sub_real_symm_ne_zero {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : IsSiegelPos Z)
    {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.IsSymm) :
    (Z - B.map (algebraMap ℝ ℂ)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw_ne, hw_eq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hzero : (dotProduct (star w) ((Z - B.map (algebraMap ℝ ℂ)) *ᵥ w)).im = 0 := by
    rw [hw_eq, dotProduct_zero, Complex.zero_im]
  let x : Fin m → ℝ := fun i => (w i).re
  let y : Fin m → ℝ := fun i => (w i).im
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h0
    push Not at h0
    apply hw_ne
    ext i
    exact Complex.ext (congrFun h0.1 i) (congrFun h0.2 i)
  have him_real : ∀ (R : Matrix (Fin m) (Fin m) ℝ), R.IsSymm →
      ∑ i, ∑ j, ((w i).re * (w j).im - (w i).im * (w j).re) * R i j = 0 := by
    intro R hR
    have h2 : (∑ i, ∑ j, ((w i).re * (w j).im - (w i).im * (w j).re) * R i j) +
        (∑ i, ∑ j, ((w i).re * (w j).im - (w i).im * (w j).re) * R i j) = 0 := by
      conv_lhs => rhs; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hsym : R j i = R i j := (Matrix.IsSymm.apply hR j i).symm
      rw [hsym]; ring
    linarith
  have him_eq : (dotProduct (star w) ((Z - B.map (algebraMap ℝ ℂ)) *ᵥ w)).im =
      (∑ i, ∑ j, x i * (Z i j).im * x j) + (∑ i, ∑ j, y i * (Z i j).im * y j) := by
    have h1 : (dotProduct (star w) ((Z - B.map (algebraMap ℝ ℂ)) *ᵥ w)).im =
        (∑ i, ∑ j, ((w i).re * (w j).im - (w i).im * (w j).re) * ((Z i j).re - B i j)) +
        ((∑ i, ∑ j, x i * (Z i j).im * x j) + (∑ i, ∑ j, y i * (Z i j).im * y j)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.map_apply,
        Complex.coe_algebraMap, Pi.star_apply, Complex.star_def, Finset.mul_sum,
        Complex.im_sum, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, x, y]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hRsymm : (Matrix.of (fun i j => (Z i j).re - B i j)).IsSymm := by
      ext i j
      simp [Matrix.transpose_apply, isSiegelPos_re_symm hZ i j, Matrix.IsSymm.apply hB i j]
    have h0 := him_real (Matrix.of (fun i j => (Z i j).re - B i j)) hRsymm
    simp only [Matrix.of_apply] at h0
    linarith
  rw [him_eq] at hzero
  have hxnn : 0 ≤ ∑ i, ∑ j, x i * (Z i j).im * x j := by
    by_cases hx : x = 0
    · simp [hx]
    · exact le_of_lt (hZ.2 x hx)
  have hynn : 0 ≤ ∑ i, ∑ j, y i * (Z i j).im * y j := by
    by_cases hy : y = 0
    · simp [hy]
    · exact le_of_lt (hZ.2 y hy)
  rcases hxy with hx | hy
  · linarith [hZ.2 x hx, hynn]
  · linarith [hZ.2 y hy, hxnn]

/-- Real Householder reflection `I - 2 u uᵀ`. -/
def reflMat {m : ℕ} (u : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - (2 : ℝ) • Matrix.of (fun i j => u i * u j)

lemma reflMat_isSymm {m : ℕ} (u : Fin m → ℝ) : (reflMat u).IsSymm := by
  ext i j
  simp [reflMat, Matrix.transpose_apply, Matrix.one_apply, eq_comm, mul_comm]

lemma reflMat_mul_self {m : ℕ} {u : Fin m → ℝ} (hu : dotProduct u u = 1) :
    reflMat u * reflMat u = 1 := by
  ext i j
  simp only [reflMat, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  have hsum : ∑ k : Fin m, (if i = k then (1 : ℝ) else 0) * (if k = j then 1 else 0) =
      if i = j then 1 else 0 := by
    simp [Finset.sum_ite_eq']
  have hsum1 : ∑ k : Fin m, (if i = k then (1 : ℝ) else 0) * (2 * (u k * u j)) =
      2 * (u i * u j) := by simp
  have hsum2 : ∑ k : Fin m, (2 * (u i * u k)) * (if k = j then (1 : ℝ) else 0) =
      2 * (u i * u j) := by simp
  have hsum3 : ∑ k : Fin m, (2 * (u i * u k)) * (2 * (u k * u j)) = 4 * (u i * u j) := by
    have : ∑ k : Fin m, (2 * (u i * u k)) * (2 * (u k * u j)) =
        (4 * (u i * u j)) * ∑ k : Fin m, u k * u k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [this, show ∑ k : Fin m, u k * u k = dotProduct u u from rfl, hu, mul_one]
  have hexp : ∀ k : Fin m,
      ((if i = k then (1 : ℝ) else 0) - 2 * (u i * u k)) *
        ((if k = j then (1 : ℝ) else 0) - 2 * (u k * u j)) =
      (if i = k then (1 : ℝ) else 0) * (if k = j then 1 else 0) -
        (if i = k then (1 : ℝ) else 0) * (2 * (u k * u j)) -
        (2 * (u i * u k)) * (if k = j then (1 : ℝ) else 0) +
        (2 * (u i * u k)) * (2 * (u k * u j)) := fun k => by ring
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hsum1, hsum2, hsum3]
  ring

lemma reflMat_swap {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    ∃ u : Fin m → ℝ, dotProduct u u = 1 ∧ reflMat u = permMat (Equiv.swap i j) := by
  let u : Fin m → ℝ := fun k =>
    (if k = i then (1 : ℝ) else if k = j then -1 else 0) / Real.sqrt 2
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨u, ?_, ?_⟩
  · simp only [dotProduct, u]
    have hterm : ∀ k : Fin m,
        ((if k = i then (1 : ℝ) else if k = j then -1 else 0) / Real.sqrt 2) *
          ((if k = i then (1 : ℝ) else if k = j then -1 else 0) / Real.sqrt 2) =
        if k = i then (1 / 2 : ℝ) else if k = j then (1 / 2 : ℝ) else 0 := by
      intro k
      split_ifs with h1 h2
      · rw [div_mul_div_comm, hsq]; ring
      · rw [div_mul_div_comm, hsq]; ring
      · simp
    simp_rw [hterm]
    have hsplit : ∑ k : Fin m, (if k = i then (1 / 2 : ℝ) else if k = j then 1 / 2 else 0) =
        (1 / 2 : ℝ) + ∑ k ∈ Finset.univ.erase i, (if k = j then (1 / 2 : ℝ) else 0) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [if_true]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_neg (Finset.ne_of_mem_erase hk)]
    have h2 : ∑ k ∈ Finset.univ.erase i, (if k = j then (1 / 2 : ℝ) else 0) = 1 / 2 := by
      rw [Finset.sum_ite_eq']
      simp [hij.symm]
    linarith [hsplit, h2]
  · ext a b
    simp only [reflMat, permMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, u]
    have hdiv2 : ∀ x y : ℝ, (x / Real.sqrt 2) * (y / Real.sqrt 2) = x * y / 2 := fun x y => by
      rw [div_mul_div_comm, hsq]
    rw [hdiv2]
    by_cases hai : a = i
    · by_cases hbi : b = i
      · rw [hai, hbi]; simp [hij, hij.symm, Equiv.swap_apply_left]
      · by_cases hbj : b = j
        · rw [hai, hbj]; simp [hij, hij.symm, Equiv.swap_apply_left]; norm_num
        · rw [hai]; simp [hbi, hbj, Equiv.swap_apply_left, Ne.symm hbi, Ne.symm hbj]
    · by_cases haj : a = j
      · by_cases hbi : b = i
        · rw [haj, hbi]; simp [hij.symm, Equiv.swap_apply_right]; norm_num
        · by_cases hbj : b = j
          · rw [haj, hbj]; simp [hij, hij.symm, Equiv.swap_apply_right]
          · rw [haj]; simp [hbi, hbj, hij.symm, Equiv.swap_apply_right, Ne.symm hbi, Ne.symm hbj]
      · by_cases hbi : b = i
        · simp [hai, haj, hbi, hij, Equiv.swap_apply_of_ne_of_ne hai haj, Ne.symm hai]
        · by_cases hbj : b = j
          · simp [hai, haj, hbi, hbj, hij, Equiv.swap_apply_of_ne_of_ne hai haj, Ne.symm haj]
          · simp [hai, haj, hbi, hbj, Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Householder orthogonal matrix mapping `e₀` to a unit vector `v`. -/
lemma exists_householder {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : dotProduct v v = 1) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ U *ᵥ Pi.single 0 1 = v := by
  let e0 : Fin (n + 1) → ℝ := Pi.single 0 1
  by_cases hve : v = e0
  · refine ⟨1, by simp, by simp, ?_⟩
    rw [Matrix.one_mulVec, hve]
  · let d : Fin (n + 1) → ℝ := fun k => e0 k - v k
    have hd_pos : 0 < dotProduct d d := by
      have hne : d ≠ 0 := by
        intro h0
        apply hve
        ext k
        have := congrFun h0 k
        simp only [d, Pi.zero_apply, sub_eq_zero] at this
        exact this.symm
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
      exact Finset.sum_pos' (fun i _ => mul_self_nonneg (d i))
        ⟨k, Finset.mem_univ k, mul_self_pos.mpr hk⟩
    have hd_val : dotProduct d d = 2 * (1 - v 0) := by
      have he0 : dotProduct e0 e0 = 1 := by simp [dotProduct, e0, Pi.single_apply]
      have he0v : dotProduct e0 v = v 0 := by simp [dotProduct, e0, Pi.single_apply]
      have hve0 : dotProduct v e0 = v 0 := by rw [dotProduct_comm, he0v]
      have h1 : dotProduct d d = dotProduct e0 e0 - dotProduct e0 v - dotProduct v e0 + dotProduct v v := by
        simp only [dotProduct, d]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [h1, he0, he0v, hve0, hv]; ring
    let w : Fin (n + 1) → ℝ := fun k => d k / Real.sqrt (dotProduct d d)
    have hw : dotProduct w w = 1 := by
      have hsq : Real.sqrt (dotProduct d d) * Real.sqrt (dotProduct d d) = dotProduct d d :=
        Real.mul_self_sqrt (le_of_lt hd_pos)
      calc dotProduct w w
          = ∑ k : Fin (n + 1), d k / Real.sqrt (dotProduct d d) * (d k / Real.sqrt (dotProduct d d)) := rfl
        _ = (∑ k : Fin (n + 1), d k * d k) / dotProduct d d := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun k _ => by rw [div_mul_div_comm, hsq]
        _ = dotProduct d d / dotProduct d d := rfl
        _ = 1 := div_self (ne_of_gt hd_pos)
    refine ⟨reflMat w, ?_, ?_, ?_⟩
    · rw [(reflMat_isSymm w).eq, reflMat_mul_self hw]
    · rw [(reflMat_isSymm w).eq, reflMat_mul_self hw]
    · ext k
      simp only [reflMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hsum : ((Matrix.of fun i j => w i * w j) *ᵥ Pi.single 0 1) k = w k * w 0 := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hsum]
      simp only [Pi.single_apply]
      have hsq : Real.sqrt (dotProduct d d) * Real.sqrt (dotProduct d d) = dotProduct d d :=
        Real.mul_self_sqrt (le_of_lt hd_pos)
      have hprod : 2 * (w k * w 0) = d k := by
        simp only [w, div_mul_div_comm, hsq]
        have hd0 : d 0 = 1 - v 0 := by simp [d, e0]
        rw [hd0, hd_val]
        have h1v : 1 - v 0 ≠ 0 := by linarith
        field_simp [h1v]
      rw [hprod]
      simp only [d, e0, Pi.single_apply]
      ring

/-- Complex rank-1 matrix `u uᵀ` for a real vector `u`. -/
def rankOne {m : ℕ} (u : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of (fun i j => (u i : ℂ) * (u j : ℂ))

/-- Top-left entry unit matrix `E₀₀`. -/
def e00Mat (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then (1 : ℂ) else 0

lemma det_add_smul_e00 {n : ℕ} (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (t : ℂ) :
    (N + t • e00Mat n).det = N.det + t * (N.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : (N + t • e00Mat n) 0 0 = N 0 0 + t := by simp [e00Mat]
  have hsub0 : (N + t • e00Mat n).submatrix Fin.succ (Fin.succAbove 0) =
      N.submatrix Fin.succ (Fin.succAbove 0) := by
    ext i j
    simp [e00Mat, Fin.succ_ne_zero]
  have htail : ∀ j : Fin n,
      (-1 : ℂ) ^ (j.succ : ℕ) * (N + t • e00Mat n) 0 j.succ *
        ((N + t • e00Mat n).submatrix Fin.succ (Fin.succAbove j.succ)).det =
      (-1 : ℂ) ^ (j.succ : ℕ) * N 0 j.succ * (N.submatrix Fin.succ (Fin.succAbove j.succ)).det := by
    intro j
    have he : (N + t • e00Mat n) 0 j.succ = N 0 j.succ := by
      simp [e00Mat, Fin.succ_ne_zero]
    have hs : (N + t • e00Mat n).submatrix Fin.succ (Fin.succAbove j.succ) =
        N.submatrix Fin.succ (Fin.succAbove j.succ) := by
      ext a b
      simp [e00Mat, Fin.succ_ne_zero]
    rw [he, hs]
  simp_rw [htail]
  rw [h0, hsub0, show Fin.succAbove (0 : Fin (n + 1)) = Fin.succ from rfl]
  simp only [Fin.val_zero, pow_zero, one_mul]
  ring

lemma householder_rankOne {n : ℕ} {v : Fin (n + 1) → ℝ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hUtU : Uᵀ * U = 1) (hUe : U *ᵥ Pi.single 0 1 = v) :
    (U.map (algebraMap ℝ ℂ))ᵀ * rankOne v * U.map (algebraMap ℝ ℂ) = e00Mat n := by
  have hUtv : Uᵀ *ᵥ v = Pi.single 0 1 := by
    rw [← hUe, Matrix.mulVec_mulVec, hUtU, Matrix.one_mulVec]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, rankOne, Matrix.of_apply,
    Complex.coe_algebraMap, e00Mat]
  have h1 : ∀ k, (∑ l, (U l i : ℂ) * ((v l : ℂ) * (v k : ℂ))) =
      ((Uᵀ *ᵥ v) i : ℂ) * (v k : ℂ) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => by ring
  simp_rw [h1]
  have h2 : ∑ k, ((Uᵀ *ᵥ v) i : ℂ) * (v k : ℂ) * (U k j : ℂ) =
      ((Uᵀ *ᵥ v) i : ℂ) * ((Uᵀ *ᵥ v) j : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Complex.ofReal_sum,
      Complex.ofReal_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h2, hUtv]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [Pi.single_apply, hi, hj]

lemma map_ofReal_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    (A * B).map (algebraMap ℝ ℂ) = A.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ) := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

lemma map_ofReal_one {m : ℕ} :
    (1 : Matrix (Fin m) (Fin m) ℝ).map (algebraMap ℝ ℂ) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

lemma det_add_smul_rankOne_eq {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    {v : Fin (n + 1) → ℝ} {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hUtU : Uᵀ * U = 1) (hUe : U *ᵥ Pi.single 0 1 = v) (t : ℂ) :
    (M + t • rankOne v).det =
      M.det + t * (((U.map (algebraMap ℝ ℂ))ᵀ * M * U.map (algebraMap ℝ ℂ)).submatrix Fin.succ Fin.succ).det := by
  set Uc : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := U.map (algebraMap ℝ ℂ)
  have hUc_orth : Ucᵀ * Uc = 1 := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) hUtU
    rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
  have hUc_det : Ucᵀ.det * Uc.det = 1 := by
    rw [← Matrix.det_mul, hUc_orth, Matrix.det_one]
  have hconj : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, (Ucᵀ * X * Uc).det = X.det := by
    intro X
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hUc_det, one_mul]
  rw [← hconj (M + t • rankOne v), ← hconj M]
  have hdist : Ucᵀ * (M + t • rankOne v) * Uc =
      Ucᵀ * M * Uc + t • (Ucᵀ * rankOne v * Uc) := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul]
  rw [hdist, householder_rankOne hUtU hUe, det_add_smul_e00]

lemma householder_reflMat_submatrix {n : ℕ} {v : Fin (n + 1) → ℝ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hUtU : Uᵀ * U = 1) (hUe : U *ᵥ Pi.single 0 1 = v)
    (W B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ((U.map (algebraMap ℝ ℂ))ᵀ *
        (((reflMat v).map (algebraMap ℝ ℂ)) * W * ((reflMat v).map (algebraMap ℝ ℂ)) - B) *
        U.map (algebraMap ℝ ℂ)).submatrix Fin.succ Fin.succ =
      ((U.map (algebraMap ℝ ℂ))ᵀ * (W - B) * U.map (algebraMap ℝ ℂ)).submatrix Fin.succ Fin.succ := by
  set Uc : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := U.map (algebraMap ℝ ℂ)
  set Sc : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (reflMat v).map (algebraMap ℝ ℂ)
  have hUc_orth : Uc * Ucᵀ = 1 := by
    have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hUtU
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) hUUt
    rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
  have hUtU_c : Ucᵀ * Uc = 1 := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) hUtU
    rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
  have hD : Ucᵀ * Sc * Uc = Matrix.diagonal (fun k : Fin (n + 1) => if k = 0 then (-1 : ℂ) else 1) := by
    have hSc : Sc = 1 - (2 : ℂ) • rankOne v := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Sc, reflMat, rankOne]
      · simp [Sc, reflMat, rankOne, Matrix.one_apply, hij]
    rw [hSc]
    have h1 : Ucᵀ * (1 - (2 : ℂ) • rankOne v) * Uc =
        Ucᵀ * Uc - (2 : ℂ) • (Ucᵀ * rankOne v * Uc) := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul]
    rw [h1, hUtU_c, householder_rankOne hUtU hUe]
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, e00Mat, Matrix.of_apply,
      smul_eq_mul, Matrix.diagonal_apply]
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj; norm_num
      · simp [hj, Ne.symm hj]
    · by_cases hj : j = 0
      · subst hj; simp [hi]
      · simp [hi, hj]
  have hprod : Ucᵀ * (Sc * W * Sc - B) * Uc =
      (Ucᵀ * Sc * Uc) * (Ucᵀ * W * Uc) * (Ucᵀ * Sc * Uc) - Ucᵀ * B * Uc := by
    have h1 : Ucᵀ * (Sc * W * Sc) * Uc =
        (Ucᵀ * Sc * Uc) * (Ucᵀ * W * Uc) * (Ucᵀ * Sc * Uc) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uc Ucᵀ, hUc_orth, Matrix.one_mul]
      rw [← Matrix.mul_assoc Uc Ucᵀ, hUc_orth, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1]
  have hprod2 : Ucᵀ * (W - B) * Uc = Ucᵀ * W * Uc - Ucᵀ * B * Uc := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hprod, hprod2, hD]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Fin.succ_ne_zero]

/-- Weighted sum of shifted determinants over `S_m`. -/
noncomputable def weightedDet {m : ℕ} (w : Equiv.Perm (Fin m) → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin m),
    (w σ : ℂ) * (((permMat σ).map (algebraMap ℝ ℂ))ᵀ * Z * ((permMat σ).map (algebraMap ℝ ℂ)) -
      B.map (algebraMap ℝ ℂ)).det

lemma permMat_mul {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permMat (σ * τ) = permMat τ * permMat σ := by
  ext i j
  simp only [permMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Matrix.mul_apply, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Finset.sum_eq_single (τ i)]
  · simp
  · intro x _ hx; simp [hx, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma permMat_one {m : ℕ} : permMat (1 : Equiv.Perm (Fin m)) = 1 := by
  ext i j
  simp [permMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Matrix.one_apply, eq_comm]

lemma permMat_transpose {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (permMat σ)ᵀ = permMat σ⁻¹ := by
  ext i j
  simp [permMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.Perm.inv_def, Equiv.eq_symm_apply, eq_comm]

lemma permMat_orth {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (permMat σ)ᵀ * permMat σ = 1 := by
  rw [permMat_transpose, ← permMat_mul, mul_inv_cancel, permMat_one]

/-- Small-ball Siegel positivity around `Z`. -/
lemma isSiegelPos_add_small_scalar {n : ℕ} {Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hZ : IsSiegelPos Z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s‖ ≤ δ → IsSiegelPos (Z + s • 1) := by
  let S : Set (Fin (n + 1) → ℝ) := {v | ∑ i, v i ^ 2 = 1}
  have hS_comp : IsCompact S := by
    have hclosed : IsClosed S := isClosed_eq
      (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const
    have hsub : S ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
      intro v hv i _
      have hle : v i ^ 2 ≤ 1 := by
        have h1 : v i ^ 2 ≤ ∑ j : Fin (n + 1), v j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
        linarith [hv.out]
      exact abs_le.mp (by nlinarith [sq_abs (v i)])
    exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hsub
  have hS_ne : S.Nonempty := ⟨Pi.single 0 1, by simp [S, Pi.single_apply]⟩
  let qf : (Fin (n + 1) → ℝ) → ℝ := fun v => ∑ i, ∑ j, v i * (Z i j).im * v j
  have hqf_cont : Continuous qf := continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ =>
      ((continuous_apply i).mul continuous_const).mul (continuous_apply j)
  obtain ⟨v0, hv0_mem, hv0_min⟩ := hS_comp.exists_isMinOn hS_ne hqf_cont.continuousOn
  have hv0_ne : v0 ≠ 0 := by
    intro h0
    have := hv0_mem.out
    simp [h0] at this
  have hc_pos : 0 < qf v0 := hZ.2 v0 hv0_ne
  refine ⟨qf v0 / 2, by linarith, fun s hs => ?_⟩
  refine ⟨hZ.1.add (by ext i j; simp [Matrix.one_apply, eq_comm]), fun v hv => ?_⟩
  have hvnorm_pos : 0 < ∑ i, v i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun j _ => sq_nonneg (v j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  let r := Real.sqrt (∑ i, v i ^ 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hvnorm_pos
  have hr_sq : r ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt (le_of_lt hvnorm_pos)
  let vhat : Fin (n + 1) → ℝ := fun i => v i / r
  have hvhat_mem : vhat ∈ S := by
    simp only [S, Set.mem_setOf_eq, vhat, div_pow, ← Finset.sum_div, ← hr_sq]
    exact div_self (ne_of_gt (sq_pos_of_pos hr_pos))
  have hqf_ge : qf v0 ≤ qf vhat := hv0_min hvhat_mem
  have hqf_scale : qf v = r ^ 2 * qf vhat := by
    simp only [qf, vhat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    field_simp [hr_ne]
  have hsum_eq : ∑ i, ∑ j, v i * ((Z + s • 1) i j).im * v j =
      qf v + s.im * (∑ i, v i ^ 2) := by
    simp only [qf, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Complex.add_im]
    have hdiag : ∑ i, ∑ j, v i * ((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i j).im * v j =
        s.im * ∑ i, v i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : ∑ j : Fin (n + 1), v i * ((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i j).im * v j =
          v i * s.im * v i := by
        trans ∑ j : Fin (n + 1), if i = j then v i * s.im * v i else 0
        · refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · simp
      rw [this]; ring
    rw [← hdiag]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, Matrix.one_apply]
    ring
  rw [hsum_eq, hqf_scale, ← hr_sq]
  have hsim : -s.im ≤ qf v0 / 2 := by
    have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    linarith [(abs_le.mp (le_trans h1 hs)).1]
  nlinarith [sq_pos_of_pos hr_pos]

/-- Small-circle argument: if `aPoly(0) ≠ 0`, `bPoly ≠ 0`, `bPoly(0) = 0`, then arbitrarily close
to `0` there is `s` with `bPoly(s) ≠ 0` and `Im(aPoly(s) / bPoly(s)) < 0`. -/
lemma exists_small_neg_im_ratio {aPoly bPoly : ℂ[X]}
    (ha0 : aPoly.eval 0 ≠ 0) (hb_ne : bPoly ≠ 0) (hb0 : bPoly.eval 0 = 0)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ s : ℂ, ‖s‖ ≤ δ ∧ bPoly.eval s ≠ 0 ∧ (aPoly.eval s / bPoly.eval s).im < 0 := by
  let k : ℕ := bPoly.rootMultiplicity 0
  have hk_pos : 1 ≤ k := by
    have := (Polynomial.rootMultiplicity_pos hb_ne).mpr hb0
    omega
  obtain ⟨g, hg_eq⟩ := Polynomial.pow_rootMultiplicity_dvd bPoly 0
  have hg0 : g.eval 0 ≠ 0 := by
    intro hg0'
    have hdvd : (X - C (0 : ℂ)) ∣ g := Polynomial.dvd_iff_isRoot.mpr hg0'
    have hdvd' : (X - C (0 : ℂ)) ^ (k + 1) ∣ bPoly := by
      rw [pow_succ, hg_eq]
      exact mul_dvd_mul_left _ hdvd
    have hle := (Polynomial.le_rootMultiplicity_iff hb_ne).mpr hdvd'
    omega
  have hg_eq' : ∀ s : ℂ, bPoly.eval s = s ^ k * g.eval s := by
    intro s
    have := congrArg (Polynomial.eval s) hg_eq
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] using this
  let L : ℂ := aPoly.eval 0 / g.eval 0
  have hL_ne : L ≠ 0 := div_ne_zero ha0 hg0
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL_ne
  have hcont : ContinuousAt (fun s : ℂ => aPoly.eval s / g.eval s) 0 :=
    (aPoly.continuous.continuousAt).div (g.continuous.continuousAt) hg0
  have hg_cont : ContinuousAt (fun s : ℂ => g.eval s) 0 := g.continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont hg_cont
  obtain ⟨δ1, hδ1_pos, hδ1⟩ := hcont (‖L‖ / 2) (by linarith)
  obtain ⟨δ2, hδ2_pos, hδ2⟩ := hg_cont (‖g.eval 0‖) (norm_pos_iff.mpr hg0)
  let r : ℝ := min (min δ (δ1 / 2)) (δ2 / 2)
  have hr_pos : 0 < r := lt_min (lt_min hδ_pos (by linarith)) (by linarith)
  let θ : ℝ := (Complex.arg L + Real.pi / 2) / (k : ℝ)
  let s : ℂ := (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hs_norm : ‖s‖ = r := by
    simp [s, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr_pos]
  have hs_ne : s ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hs_norm; linarith
  have hg_s_ne : g.eval s ≠ 0 := by
    have hdist : dist s 0 < δ2 := by
      rw [dist_zero_right, hs_norm]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have := hδ2 hdist
    intro h0
    rw [h0, dist_zero_left] at this
    exact lt_irrefl _ this
  have hb_s_ne : bPoly.eval s ≠ 0 := by
    rw [hg_eq' s]
    exact mul_ne_zero (pow_ne_zero k hs_ne) hg_s_ne
  have hsk : s ^ k = (r ^ k : ℂ) * (Complex.I * (L / (‖L‖ : ℂ))) := by
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hexp : (Complex.exp (Complex.I * (θ : ℂ))) ^ k = Complex.I * (L / (‖L‖ : ℂ)) := by
      rw [← Complex.exp_nat_mul]
      have harg : (k : ℂ) * (Complex.I * (θ : ℂ)) =
          Complex.I * (Complex.arg L : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
        have hθ : (θ : ℂ) = ((Complex.arg L : ℂ) + ((Real.pi / 2 : ℝ) : ℂ)) / (k : ℂ) := by
          simp only [θ, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast]
        rw [hθ]
        have hkne' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [hkne']
      rw [harg, Complex.exp_add, Complex.exp_mul_I]
      have hcos : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
        rw [← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
      have hsin : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
      rw [hcos, hsin, zero_add, one_mul]
      have hpolar : (‖L‖ : ℂ) * Complex.exp ((Complex.arg L : ℂ) * Complex.I) = L :=
        Complex.norm_mul_exp_arg_mul_I L
      rw [mul_comm Complex.I (Complex.arg L : ℂ)]
      have hL_norm_ne : (‖L‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hL_pos)
      rw [mul_comm _ Complex.I]
      congr 1
      exact eq_div_of_mul_eq hL_norm_ne (by rw [mul_comm, hpolar])
    simp only [s, mul_pow, hexp]
  have hL_div : L / s ^ k = -Complex.I * ((‖L‖ / r ^ k : ℝ) : ℂ) := by
    have hrk_ne : (r ^ k : ℂ) ≠ 0 := pow_ne_zero k (Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos))
    have hL_norm_ne : (‖L‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hL_pos)
    rw [hsk]
    push_cast
    field_simp [hrk_ne, hL_norm_ne, hL_ne]
    ring_nf
    simp [Complex.I_sq]
  have hclose : ‖aPoly.eval s / bPoly.eval s - L / s ^ k‖ < ‖L‖ / (2 * r ^ k) := by
    have hdist1 : dist s 0 < δ1 := by
      rw [dist_zero_right, hs_norm]
      exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
    have h1 := hδ1 hdist1
    rw [Complex.dist_eq] at h1
    have heq : aPoly.eval s / bPoly.eval s - L / s ^ k =
        (aPoly.eval s / g.eval s - L) / s ^ k := by
      rw [hg_eq' s]; field_simp [pow_ne_zero k hs_ne, hg_s_ne]
    rw [heq, norm_div, norm_pow, hs_norm]
    have hrk_pos : 0 < r ^ k := pow_pos hr_pos k
    rw [div_lt_div_iff₀ hrk_pos (by positivity)]
    nlinarith
  have him_neg : (aPoly.eval s / bPoly.eval s).im < 0 := by
    have h1 : |(aPoly.eval s / bPoly.eval s - L / s ^ k).im| ≤
        ‖aPoly.eval s / bPoly.eval s - L / s ^ k‖ := Complex.abs_im_le_norm _
    have h2 : (L / s ^ k).im = -(‖L‖ / r ^ k) := by
      rw [hL_div, neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have h3 : (aPoly.eval s / bPoly.eval s).im - (L / s ^ k).im ≤
        |(aPoly.eval s / bPoly.eval s - L / s ^ k).im| := by
      rw [← Complex.sub_im]; exact le_abs_self _
    have hrk_pos : 0 < r ^ k := pow_pos hr_pos k
    have hhalf : ‖L‖ / (2 * r ^ k) < ‖L‖ / r ^ k := by
      rw [div_lt_div_iff₀ (by positivity) hrk_pos]; nlinarith
    linarith
  exact ⟨s, by rw [hs_norm]; exact le_trans (min_le_left _ _) (min_le_left _ _), hb_s_ne, him_neg⟩

/-- A single reflection step preserves real-stability of `weightedDet` on `IsSiegelPos`! -/
lemma weightedDet_refl_stable {n : ℕ} {w : Equiv.Perm (Fin (n + 1)) → ℝ}
    (hw_sum : ∑ σ, w σ = 1)
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hstable : ∀ Z, IsSiegelPos Z → weightedDet w B Z ≠ 0)
    {u : Fin (n + 1) → ℝ} (hu : dotProduct u u = 1)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hZ : IsSiegelPos Z) :
    (q : ℂ) * weightedDet w B Z +
      ((1 - q : ℝ) : ℂ) * weightedDet w B
        (((reflMat u).map (algebraMap ℝ ℂ))ᵀ * Z * ((reflMat u).map (algebraMap ℝ ℂ))) ≠ 0 := by
  have hv_unit : ∀ σ : Equiv.Perm (Fin (n + 1)),
      dotProduct ((permMat σ)ᵀ *ᵥ u) ((permMat σ)ᵀ *ᵥ u) = 1 := by
    intro σ
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
    have h1 : permMat σ * (permMat σ)ᵀ = 1 := mul_eq_one_comm.mp (permMat_orth σ)
    rw [h1, Matrix.one_mulVec, hu]
  choose U hUtU _hUUt hUe using fun σ => exists_householder (hv_unit σ)
  let Pc : Equiv.Perm (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun σ => (permMat σ).map (algebraMap ℝ ℂ)
  let Uc : Equiv.Perm (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun σ => (U σ).map (algebraMap ℝ ℂ)
  let b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ℂ := fun W =>
    ∑ σ : Equiv.Perm (Fin (n + 1)), (w σ : ℂ) *
      (((Uc σ)ᵀ * ((Pc σ)ᵀ * W * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ).submatrix Fin.succ Fin.succ).det
  have hlin : ∀ W (t : ℂ), weightedDet w B (W + t • rankOne u) = weightedDet w B W + t * b W := by
    intro W t
    simp only [weightedDet, b, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hr1 : (Pc σ)ᵀ * rankOne u * Pc σ = rankOne ((permMat σ)ᵀ *ᵥ u) := by
      ext i j
      simp only [Pc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, rankOne,
        Matrix.of_apply, Complex.coe_algebraMap, Matrix.mulVec, dotProduct]
      have h1 : ∀ k, (∑ l, (permMat σ l i : ℂ) * ((u l : ℂ) * (u k : ℂ))) =
          (∑ l, (permMat σ l i : ℂ) * (u l : ℂ)) * (u k : ℂ) := fun k => by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => by ring
      simp_rw [h1]
      have h2 : ∑ x, (∑ l, (permMat σ l i : ℂ) * (u l : ℂ)) * (u x : ℂ) * (permMat σ x j : ℂ) =
          (∑ l, (permMat σ l i : ℂ) * (u l : ℂ)) * (∑ x, (permMat σ x j : ℂ) * (u x : ℂ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [h2]
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    have hdist : (Pc σ)ᵀ * (W + t • rankOne u) * Pc σ - B.map (algebraMap ℝ ℂ) =
        ((Pc σ)ᵀ * W * Pc σ - B.map (algebraMap ℝ ℂ)) + t • rankOne ((permMat σ)ᵀ *ᵥ u) := by
      rw [← hr1]
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, add_sub_right_comm]
    rw [hdist, det_add_smul_rankOne_eq _ (hUtU σ) (hUe σ) t]
    ring
  set Sc : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (reflMat u).map (algebraMap ℝ ℂ)
  have hSc_symm : Scᵀ = Sc := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) (reflMat_isSymm u).eq
    rwa [Matrix.transpose_map] at this
  have hb_refl : b (Scᵀ * Z * Sc) = b Z := by
    simp only [b]
    refine Finset.sum_congr rfl fun σ _ => ?_
    apply congrArg ((w σ : ℂ) * ·)
    apply congrArg Matrix.det
    have hPc_orth : Pc σ * (Pc σ)ᵀ = 1 := by
      have h1 : permMat σ * (permMat σ)ᵀ = 1 := mul_eq_one_comm.mp (permMat_orth σ)
      have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) h1
      rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
    have hSconj : (Pc σ)ᵀ * Sc * Pc σ = (reflMat ((permMat σ)ᵀ *ᵥ u)).map (algebraMap ℝ ℂ) := by
      have h1 : (permMat σ)ᵀ * reflMat u * permMat σ = reflMat ((permMat σ)ᵀ *ᵥ u) := by
        simp only [reflMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, permMat_orth,
          Matrix.smul_mul, Matrix.mul_smul]
        congr 2
        ext a b
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.mulVec, dotProduct]
        have h2 : ∀ k, (∑ l, permMat σ l a * (u l * u k)) = (∑ l, permMat σ l a * u l) * u k :=
          fun k => by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => by ring
        simp_rw [h2]
        have h3 : ∑ x, (∑ l, permMat σ l a * u l) * u x * permMat σ x b =
            (∑ l, permMat σ l a * u l) * (∑ x, permMat σ x b * u x) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
        exact h3
      have h2 := congrArg (Matrix.map · (algebraMap ℝ ℂ)) h1
      rwa [map_ofReal_mul, map_ofReal_mul, Matrix.transpose_map] at h2
    have hrew : (Pc σ)ᵀ * (Scᵀ * Z * Sc) * Pc σ - B.map (algebraMap ℝ ℂ) =
        ((reflMat ((permMat σ)ᵀ *ᵥ u)).map (algebraMap ℝ ℂ)) * ((Pc σ)ᵀ * Z * Pc σ) *
          ((reflMat ((permMat σ)ᵀ *ᵥ u)).map (algebraMap ℝ ℂ)) - B.map (algebraMap ℝ ℂ) := by
      rw [hSc_symm, ← hSconj]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Pc σ) (Pc σ)ᵀ, hPc_orth, Matrix.one_mul]
      rw [← Matrix.mul_assoc (Pc σ) (Pc σ)ᵀ, hPc_orth, Matrix.one_mul]
    rw [hrew]
    exact householder_reflMat_submatrix (hUtU σ) (hUe σ) ((Pc σ)ᵀ * Z * Pc σ) (B.map (algebraMap ℝ ℂ))
  -- Step 1: Show b Z ≠ 0
  have hbZ_ne : b Z ≠ 0 := by
    intro hb0
    let aPoly : ℂ[X] := ∑ σ : Equiv.Perm (Fin (n + 1)),
      Polynomial.C (w σ : ℂ) *
        (Matrix.scalar (Fin (n + 1)) X +
          (((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)).map Polynomial.C)).det
    let bPoly : ℂ[X] := ∑ σ : Equiv.Perm (Fin (n + 1)),
      Polynomial.C (w σ : ℂ) *
        (Matrix.scalar (Fin n) X +
          ((((Uc σ)ᵀ * ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ).submatrix
            Fin.succ Fin.succ).map Polynomial.C)).det
    have heval_det : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (s : ℂ),
        ((Matrix.scalar (Fin k) (X : ℂ[X]) + M.map Polynomial.C).det).eval s =
          (s • (1 : Matrix (Fin k) (Fin k) ℂ) + M).det := by
      intro k M s
      have hcp : (Matrix.scalar (Fin k) (X : ℂ[X]) + M.map Polynomial.C).det = (-M).charpoly := by
        rw [Matrix.charpoly, Matrix.charmatrix]
        congr 1; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, sub_eq_add_neg]
      rw [hcp, Matrix.eval_charpoly]
      congr 1; ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
    have ha_eval : ∀ s : ℂ, aPoly.eval s = weightedDet w B (Z + s • 1) := by
      intro s
      simp only [aPoly, weightedDet, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C]
      refine Finset.sum_congr rfl fun σ _ => ?_
      apply congrArg ((w σ : ℂ) * ·)
      rw [heval_det]
      apply congrArg Matrix.det
      have hPc_orth : (Pc σ)ᵀ * Pc σ = 1 := by
        have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) (permMat_orth σ)
        rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
      have h1 : (Pc σ)ᵀ * (Z + s • 1) * Pc σ - B.map (algebraMap ℝ ℂ) =
          s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
            ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) := by
        calc (Pc σ)ᵀ * (Z + s • 1) * Pc σ - B.map (algebraMap ℝ ℂ)
            = (Pc σ)ᵀ * Z * Pc σ + s • ((Pc σ)ᵀ * Pc σ) - B.map (algebraMap ℝ ℂ) := by
              simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
          _ = s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
              ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) := by
              rw [hPc_orth]; abel
      exact h1.symm
    have hb_eval : ∀ s : ℂ, bPoly.eval s = b (Z + s • 1) := by
      intro s
      simp only [bPoly, b, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
      refine Finset.sum_congr rfl fun σ _ => ?_
      apply congrArg ((w σ : ℂ) * ·)
      rw [heval_det]
      apply congrArg Matrix.det
      have hPc_orth : (Pc σ)ᵀ * Pc σ = 1 := by
        have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) (permMat_orth σ)
        rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
      have hUc_orth : (Uc σ)ᵀ * Uc σ = 1 := by
        have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) (hUtU σ)
        rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
      have h1 : (Uc σ)ᵀ * ((Pc σ)ᵀ * (Z + s • 1) * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ =
          s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
            (Uc σ)ᵀ * ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ := by
        have hp1 : (Pc σ)ᵀ * (Z + s • 1) * Pc σ - B.map (algebraMap ℝ ℂ) =
            s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
              ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) := by
          calc (Pc σ)ᵀ * (Z + s • 1) * Pc σ - B.map (algebraMap ℝ ℂ)
              = (Pc σ)ᵀ * Z * Pc σ + s • ((Pc σ)ᵀ * Pc σ) - B.map (algebraMap ℝ ℂ) := by
                simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
            _ = s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
                ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) := by
                rw [hPc_orth]; abel
        rw [hp1]
        calc (Uc σ)ᵀ * (s • 1 + ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ))) * Uc σ
            = s • ((Uc σ)ᵀ * Uc σ) + (Uc σ)ᵀ * ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ := by
              simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
          _ = s • 1 + (Uc σ)ᵀ * ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ := by
              rw [hUc_orth]
      rw [h1]
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply]
    have hbPoly_ne : bPoly ≠ 0 := by
      have hcoeff : bPoly.coeff n = 1 := by
        simp only [bPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
        have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
            (Matrix.scalar (Fin n) (X : ℂ[X]) +
              ((((Uc σ)ᵀ * ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ).submatrix
                Fin.succ Fin.succ).map Polynomial.C)).det.coeff n = 1 := by
          intro σ
          set M := (((Uc σ)ᵀ * ((Pc σ)ᵀ * Z * Pc σ - B.map (algebraMap ℝ ℂ)) * Uc σ).submatrix
            Fin.succ Fin.succ)
          have hcp : (Matrix.scalar (Fin n) (X : ℂ[X]) + M.map Polynomial.C).det = (-M).charpoly := by
            rw [Matrix.charpoly, Matrix.charmatrix]
            congr 1; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, sub_eq_add_neg]
          rw [hcp]
          have hd : (-M).charpoly.natDegree = n := by
            rw [Matrix.charpoly_natDegree_eq_dim]; simp
          have hm := (Matrix.charpoly_monic (-M)).coeff_natDegree
          rwa [hd] at hm
        simp_rw [hterm, mul_one]
        rw [← Complex.ofReal_sum, hw_sum, Complex.ofReal_one]
      intro h0
      rw [h0, Polynomial.coeff_zero] at hcoeff
      exact zero_ne_one hcoeff
    obtain ⟨δ, hδ_pos, hδ_prop⟩ := isSiegelPos_add_small_scalar hZ
    have ha0 : aPoly.eval 0 ≠ 0 := by rw [ha_eval 0]; simpa using hstable Z hZ
    have hb0' : bPoly.eval 0 = 0 := by rw [hb_eval 0]; simpa using hb0
    obtain ⟨s, hs_le, hb_s_ne, him_neg⟩ := exists_small_neg_im_ratio ha0 hbPoly_ne hb0' hδ_pos
    let t : ℂ := -(aPoly.eval s / bPoly.eval s)
    have ht_im : 0 < t.im := by simp [t]; linarith
    have hsiegel2 : IsSiegelPos (Z + s • 1 + t • rankOne u) := by
      apply isSiegelPos_add_im_nonneg (hδ_prop s hs_le)
      · ext i j; simp [rankOne, Matrix.transpose_apply, mul_comm]
      · intro v
        have heq : ∑ i, ∑ j, v i * ((t • rankOne u) i j).im * v j =
            t.im * (∑ i, v i * u i) ^ 2 := by
          simp only [rankOne, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Complex.mul_im,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
          rw [sq, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [heq]
        exact mul_nonneg (le_of_lt ht_im) (sq_nonneg _)
    have hzero : weightedDet w B (Z + s • 1 + t • rankOne u) = 0 := by
      rw [hlin (Z + s • 1) t, ← ha_eval s, ← hb_eval s]
      simp only [t]
      field_simp [hb_s_ne]
      ring
    exact hstable _ hsiegel2 hzero
  -- Step 2: Now b Z ≠ 0! Both ratios have strictly positive imaginary part!
  have him_pos : ∀ W, IsSiegelPos W → b W = b Z → 0 < (weightedDet w B W / b Z).im := by
    intro W hW hbW
    by_contra hle
    push Not at hle
    let t : ℂ := -(weightedDet w B W / b Z)
    have ht_im : 0 ≤ t.im := by simp [t]; linarith
    have hWt : IsSiegelPos (W + t • rankOne u) := by
      apply isSiegelPos_add_im_nonneg hW
      · ext i j; simp [rankOne, Matrix.transpose_apply, mul_comm]
      · intro v
        have heq : ∑ i, ∑ j, v i * ((t • rankOne u) i j).im * v j =
            t.im * (∑ i, v i * u i) ^ 2 := by
          simp only [rankOne, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Complex.mul_im,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
          rw [sq, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [heq]
        exact mul_nonneg ht_im (sq_nonneg _)
    have hzero : weightedDet w B (W + t • rankOne u) = 0 := by
      rw [hlin W t, hbW]
      simp only [t]
      field_simp [hbZ_ne]
      ring
    exact hstable _ hWt hzero
  have h1 : 0 < (weightedDet w B Z / b Z).im := him_pos Z hZ rfl
  have hZrefl : IsSiegelPos (Scᵀ * Z * Sc) :=
    isSiegelPos_conj hZ (by rw [(reflMat_isSymm u).eq, reflMat_mul_self hu])
  have h2 : 0 < (weightedDet w B (Scᵀ * Z * Sc) / b Z).im := him_pos _ hZrefl hb_refl
  intro hzero
  have hdiv : ((q : ℂ) * weightedDet w B Z + ((1 - q : ℝ) : ℂ) * weightedDet w B (Scᵀ * Z * Sc)) / b Z = 0 := by
    rw [hzero, zero_div]
  have him0 : (((q : ℂ) * weightedDet w B Z + ((1 - q : ℝ) : ℂ) * weightedDet w B (Scᵀ * Z * Sc)) / b Z).im = 0 := by
    rw [hdiv, Complex.zero_im]
  have him_comb : (((q : ℂ) * weightedDet w B Z +
      ((1 - q : ℝ) : ℂ) * weightedDet w B (Scᵀ * Z * Sc)) / b Z).im =
      q * (weightedDet w B Z / b Z).im + (1 - q) * (weightedDet w B (Scᵀ * Z * Sc) / b Z).im := by
    rw [add_div, mul_div_assoc, mul_div_assoc, Complex.add_im]
    simp [Complex.mul_im]
  rw [him_comb] at him0
  rcases hq with ⟨hq0, hq1⟩
  have hcomb_pos : 0 < q * (weightedDet w B Z / b Z).im + (1 - q) * (weightedDet w B (Scᵀ * Z * Sc) / b Z).im := by
    by_cases hqz : q = 0
    · subst hqz; linarith
    · have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      have h1q : 0 ≤ 1 - q := by linarith
      nlinarith
  linarith

end SiegelStability

/-! ### Section 3: Decomposition of uniform `Equiv.Perm (Fin m)` into independent binary swaps -/

section SwapDecomposition

def IsSwap {m : ℕ} (τ : Equiv.Perm (Fin m)) : Prop :=
  ∃ i j : Fin m, i ≠ j ∧ τ = Equiv.swap i j

def swapsDist {m : ℕ} : List (ℝ × Equiv.Perm (Fin m)) → Equiv.Perm (Fin m) → ℝ
  | [], σ => if σ = 1 then 1 else 0
  | (p, τ) :: rest, σ => p * swapsDist rest σ + (1 - p) * swapsDist rest (τ * σ)

lemma swapsDist_sum {m : ℕ} (L : List (ℝ × Equiv.Perm (Fin m))) :
    ∑ σ : Equiv.Perm (Fin m), swapsDist L σ = 1 := by
  induction L with
  | nil => simp [swapsDist]
  | cons x rest ih =>
    rcases x with ⟨p, τ⟩
    simp only [swapsDist, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hshift : ∑ σ : Equiv.Perm (Fin m), swapsDist rest (τ * σ) =
        ∑ σ : Equiv.Perm (Fin m), swapsDist rest σ :=
      Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
    rw [hshift, ih]
    ring

/-- Embed a permutation of `Fin m` into `Fin (m + 1)` fixing `Fin.last m`. -/
def embedPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) where
  toFun := Fin.lastCases (Fin.last m) (fun i => (σ i).castSucc)
  invFun := Fin.lastCases (Fin.last m) (fun i => (σ.symm i).castSucc)
  left_inv := Fin.lastCases (by simp) (fun i => by simp)
  right_inv := Fin.lastCases (by simp) (fun i => by simp)

lemma embedPerm_last {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    embedPerm σ (Fin.last m) = Fin.last m := by
  simp [embedPerm]

lemma embedPerm_castSucc {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    embedPerm σ i.castSucc = (σ i).castSucc := by
  simp [embedPerm]

lemma embedPerm_swap {m : ℕ} (i j : Fin m) :
    embedPerm (Equiv.swap i j) = Equiv.swap i.castSucc j.castSucc := by
  ext k
  refine Fin.lastCases ?_ (fun l => ?_) k
  · rw [embedPerm_last, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last i).symm
      (Fin.castSucc_ne_last j).symm]
  · rw [embedPerm_castSucc]
    by_cases h1 : l = i
    · subst h1; simp
    · by_cases h2 : l = j
      · subst h2; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.castSucc_injective _ h))
            (fun h => h2 (Fin.castSucc_injective _ h))]

def restrictPerm {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (h : σ (Fin.last m) = Fin.last m) :
    Equiv.Perm (Fin m) where
  toFun i := ⟨(σ i.castSucc).val, by
    have hne : σ i.castSucc ≠ Fin.last m := fun heq =>
      Fin.castSucc_ne_last i (σ.injective (heq.trans h.symm))
    exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (σ i.castSucc).isLt) (Fin.val_ne_of_ne hne)⟩
  invFun i := ⟨(σ.symm i.castSucc).val, by
    have hsym : σ.symm (Fin.last m) = Fin.last m := by
      calc σ.symm (Fin.last m) = σ.symm (σ (Fin.last m)) := by rw [h]
        _ = Fin.last m := σ.symm_apply_apply _
    have hne : σ.symm i.castSucc ≠ Fin.last m := fun heq =>
      Fin.castSucc_ne_last i (σ.symm.injective (heq.trans hsym.symm))
    exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (σ.symm i.castSucc).isLt) (Fin.val_ne_of_ne hne)⟩
  left_inv i := by
    apply Fin.ext
    have h1 : (⟨(σ i.castSucc).val, Nat.lt_succ_of_lt (by
      have hne : σ i.castSucc ≠ Fin.last m := fun heq =>
        Fin.castSucc_ne_last i (σ.injective (heq.trans h.symm))
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (σ i.castSucc).isLt) (Fin.val_ne_of_ne hne))⟩ : Fin (m + 1)) =
      σ i.castSucc := Fin.ext rfl
    change (σ.symm ⟨(σ i.castSucc).val, _⟩).val = i.val
    rw [show (⟨(σ i.castSucc).val, _⟩ : Fin (m + 1)) = σ i.castSucc from Fin.ext rfl,
      Equiv.symm_apply_apply]
    rfl
  right_inv i := by
    apply Fin.ext
    change (σ ⟨(σ.symm i.castSucc).val, _⟩).val = i.val
    rw [show (⟨(σ.symm i.castSucc).val, _⟩ : Fin (m + 1)) = σ.symm i.castSucc from Fin.ext rfl,
      Equiv.apply_symm_apply]
    rfl

lemma swapsDist_embed {m : ℕ} (L : List (ℝ × Equiv.Perm (Fin m)))
    (σ : Equiv.Perm (Fin (m + 1))) :
    swapsDist (L.map fun x => (x.1, embedPerm x.2)) σ =
      if h : σ (Fin.last m) = Fin.last m then
        swapsDist L (restrictPerm σ h)
      else 0 := by
  induction L generalizing σ with
  | nil =>
    simp only [List.map_nil, swapsDist]
    by_cases h1 : σ = 1
    · subst h1
      have hlast : (1 : Equiv.Perm (Fin (m + 1))) (Fin.last m) = Fin.last m := rfl
      rw [if_pos rfl, dif_pos hlast, if_pos (by ext i; simp [restrictPerm])]
    · rw [if_neg h1]
      by_cases h2 : σ (Fin.last m) = Fin.last m
      · rw [dif_pos h2, if_neg]
        intro h3
        apply h1
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact congrArg Fin.val h2
        · have := congrArg Fin.val (congrFun (congrArg Equiv.toFun h3) j)
          simpa [restrictPerm] using this
      · rw [dif_neg h2]
  | cons x rest ih =>
    rcases x with ⟨p, τ⟩
    simp only [List.map_cons, swapsDist]
    rw [ih σ, ih (embedPerm τ * σ)]
    by_cases h : σ (Fin.last m) = Fin.last m
    · have h' : (embedPerm τ * σ) (Fin.last m) = Fin.last m := by
        change embedPerm τ (σ (Fin.last m)) = Fin.last m
        rw [h, embedPerm_last]
      have lhs1 : (if h0 : σ (Fin.last m) = Fin.last m then swapsDist rest (restrictPerm σ h0) else 0) =
          swapsDist rest (restrictPerm σ h) := dif_pos h
      have lhs2 : (if h0 : (embedPerm τ * σ) (Fin.last m) = Fin.last m then
          swapsDist rest (restrictPerm (embedPerm τ * σ) h0) else 0) =
          swapsDist rest (restrictPerm (embedPerm τ * σ) h') := dif_pos h'
      have rhs1 : (if h0 : σ (Fin.last m) = Fin.last m then
          p * swapsDist rest (restrictPerm σ h0) + (1 - p) * swapsDist rest (τ * restrictPerm σ h0) else 0) =
          p * swapsDist rest (restrictPerm σ h) + (1 - p) * swapsDist rest (τ * restrictPerm σ h) := dif_pos h
      rw [lhs1, lhs2, rhs1]
      have hreq : restrictPerm (embedPerm τ * σ) h' = τ * restrictPerm σ h := by
        ext i
        change ((embedPerm τ) (σ i.castSucc)).val = (τ (restrictPerm σ h i)).val
        have hcs : σ i.castSucc = (restrictPerm σ h i).castSucc := Fin.ext rfl
        rw [hcs, embedPerm_castSucc]; rfl
      rw [hreq]
    · have h' : (embedPerm τ * σ) (Fin.last m) ≠ Fin.last m := by
        intro h0
        apply h
        have h1 : embedPerm τ (σ (Fin.last m)) = embedPerm τ (Fin.last m) := by
          rw [embedPerm_last]; exact h0
        exact (embedPerm τ).injective h1
      have lhs1 : (if h0 : σ (Fin.last m) = Fin.last m then swapsDist rest (restrictPerm σ h0) else 0) = 0 :=
        dif_neg h
      have lhs2 : (if h0 : (embedPerm τ * σ) (Fin.last m) = Fin.last m then
          swapsDist rest (restrictPerm (embedPerm τ * σ) h0) else 0) = 0 :=
        dif_neg h'
      have rhs1 : (if h0 : σ (Fin.last m) = Fin.last m then
          p * swapsDist rest (restrictPerm σ h0) + (1 - p) * swapsDist rest (τ * restrictPerm σ h0) else 0) = 0 :=
        dif_neg h
      rw [lhs1, lhs2, rhs1]
      ring

/-- Every uniform distribution on `Equiv.Perm (Fin m)` is realized by a list of independent swaps. -/
lemma exists_uniform_swaps : ∀ m : ℕ,
    ∃ L : List (ℝ × Equiv.Perm (Fin m)),
      (∀ x ∈ L, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2) ∧
      ∀ σ : Equiv.Perm (Fin m), swapsDist L σ = (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹
  | 0 => ⟨[], by simp, fun σ => by
      have h1 : σ = 1 := Subsingleton.elim _ _
      simp [swapsDist, h1]⟩
  | 1 => ⟨[], by simp, fun σ => by
      have h1 : σ = 1 := Subsingleton.elim _ _
      simp [swapsDist, h1]⟩
  | m + 2 => by
    obtain ⟨Lsub, hLsub_valid, hLsub_unif⟩ := exists_uniform_swaps (m + 1)
    let L0 : List (ℝ × Equiv.Perm (Fin (m + 2))) := Lsub.map fun x => (x.1, embedPerm x.2)
    have hL0_valid : ∀ x ∈ L0, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2 := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨⟨p, τ⟩, hmem, rfl⟩
      obtain ⟨hp, i, j, hij, rfl⟩ := hLsub_valid _ hmem
      exact ⟨hp, i.castSucc, j.castSucc, fun h => hij (Fin.castSucc_injective _ h),
        embedPerm_swap i j⟩
    have hL0_dist : ∀ σ : Equiv.Perm (Fin (m + 2)),
        swapsDist L0 σ =
          if σ (Fin.last (m + 1)) = Fin.last (m + 1) then
            ((Nat.factorial (m + 1) : ℝ))⁻¹
          else 0 := by
      intro σ
      rw [swapsDist_embed]
      split_ifs with h
      · rw [hLsub_unif]; simp [Fintype.card_perm]
      · rfl
    have hbuild : ∀ r : ℕ, r ≤ m + 1 →
        ∃ L : List (ℝ × Equiv.Perm (Fin (m + 2))),
          (∀ x ∈ L, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2) ∧
          ∀ σ : Equiv.Perm (Fin (m + 2)),
            swapsDist L σ =
              if m + 1 - r < (σ (Fin.last (m + 1))).val then
                ((Nat.factorial (m + 2) : ℝ))⁻¹
              else if (σ (Fin.last (m + 1))).val = m + 1 - r then
                ((m + 2 - r : ℕ) : ℝ) / (Nat.factorial (m + 2) : ℝ)
              else 0 := by
      intro r
      induction r with
      | zero =>
        intro _
        refine ⟨L0, hL0_valid, fun σ => ?_⟩
        rw [hL0_dist]
        have hlt : ¬ (m + 1 - 0 < (σ (Fin.last (m + 1))).val) := by
          have := (σ (Fin.last (m + 1))).isLt; omega
        rw [if_neg hlt]
        have heq_iff : (σ (Fin.last (m + 1))).val = m + 1 - 0 ↔
            σ (Fin.last (m + 1)) = Fin.last (m + 1) := by
          simp [Fin.ext_iff]
        by_cases h : σ (Fin.last (m + 1)) = Fin.last (m + 1)
        · rw [if_pos h, if_pos (heq_iff.mpr h)]
          have hfac : (Nat.factorial (m + 2) : ℝ) = ((m + 2 : ℕ) : ℝ) * (Nat.factorial (m + 1) : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          rw [Nat.sub_zero, hfac]
          have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hmf : (Nat.factorial (m + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          field_simp [hm2, hmf]
        · rw [if_neg h, if_neg (mt heq_iff.mp h)]
      | succ r ih =>
        intro hr
        obtain ⟨Lprev, hLprev_valid, hLprev_dist⟩ := ih (by omega)
        let k : ℕ := m + 1 - r
        let a : Fin (m + 2) := ⟨k - 1, by omega⟩
        let b : Fin (m + 2) := ⟨k, by omega⟩
        have hab : a ≠ b := by
          intro h; have := congrArg Fin.val h; simp [a, b] at this; omega
        let p : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
        refine ⟨(p, Equiv.swap a b) :: Lprev, ?_, fun σ => ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · refine ⟨⟨by positivity, ?_⟩, a, b, hab, rfl⟩
            rw [div_le_one (by positivity)]
            exact_mod_cast (show 1 ≤ k + 1 by omega)
          · exact hLprev_valid x hmem
        · simp only [swapsDist]
          rw [hLprev_dist σ, hLprev_dist (Equiv.swap a b * σ)]
          have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hfac_ne : (Nat.factorial (m + 2) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hm2r : m + 2 - r = k + 1 := by omega
          have hm1r : m + 1 - (r + 1) = k - 1 := by omega
          have hm2r1 : m + 2 - (r + 1) = k := by omega
          set v := σ (Fin.last (m + 1))
          have hτv : (Equiv.swap a b * σ) (Fin.last (m + 1)) = Equiv.swap a b v := rfl
          rw [hτv]
          change p * (if k < v.val then ((Nat.factorial (m + 2) : ℝ))⁻¹
              else if v.val = k then ((m + 2 - r : ℕ) : ℝ) / (Nat.factorial (m + 2) : ℝ) else 0) +
            (1 - p) * (if k < (Equiv.swap a b v).val then ((Nat.factorial (m + 2) : ℝ))⁻¹
              else if (Equiv.swap a b v).val = k then ((m + 2 - r : ℕ) : ℝ) / (Nat.factorial (m + 2) : ℝ) else 0) =
            if m + 1 - (r + 1) < v.val then ((Nat.factorial (m + 2) : ℝ))⁻¹
              else if v.val = m + 1 - (r + 1) then ((m + 2 - (r + 1) : ℕ) : ℝ) / (Nat.factorial (m + 2) : ℝ) else 0
          rw [hm2r, hm1r, hm2r1]
          by_cases hv_gt : k < v.val
          · have hva : v ≠ a := fun h => by rw [h] at hv_gt; simp [a] at hv_gt; omega
            have hvb : v ≠ b := fun h => by rw [h] at hv_gt; simp [b] at hv_gt
            rw [Equiv.swap_apply_of_ne_of_ne hva hvb, if_pos hv_gt, if_pos (by omega : k - 1 < v.val)]
            ring
          · by_cases hv_eq : v.val = k
            · have hvb : v = b := Fin.ext hv_eq
              rw [hvb, Equiv.swap_apply_right]
              simp only [a, b, lt_irrefl, if_false, if_true]
              rw [if_neg (by omega : ¬ k < k - 1), if_neg (by omega : ¬ k - 1 = k),
                if_pos (by omega : k - 1 < k)]
              simp only [p]
              field_simp [hk1_ne, hfac_ne]
              ring
            · by_cases hv_prev : v.val = k - 1
              · have hva : v = a := Fin.ext hv_prev
                rw [hva, Equiv.swap_apply_left]
                simp only [a, b, lt_irrefl, if_false, if_true]
                rw [if_neg (by omega : ¬ k < k - 1), if_neg (by omega : ¬ k - 1 = k)]
                simp only [p]
                push_cast
                field_simp [hk1_ne, hfac_ne]
                ring
              · have hva : v ≠ a := fun h => hv_prev (by rw [h])
                have hvb : v ≠ b := fun h => hv_eq (by rw [h])
                rw [Equiv.swap_apply_of_ne_of_ne hva hvb, if_neg hv_gt, if_neg hv_eq,
                  if_neg (by omega : ¬ k - 1 < v.val), if_neg hv_prev]
                ring
    obtain ⟨L, hL_valid, hL_dist⟩ := hbuild (m + 1) le_rfl
    refine ⟨L, hL_valid, fun σ => ?_⟩
    rw [hL_dist σ]
    simp only [Nat.sub_self, show m + 2 - (m + 1) = 1 by omega, Nat.cast_one, one_div,
      Fintype.card_perm, Fintype.card_fin]
    by_cases h0 : 0 < (σ (Fin.last (m + 1))).val
    · rw [if_pos h0]
    · rw [if_neg h0, if_pos (by omega)]

end SwapDecomposition

/-! ### Section 4: Binary tree descent for `A.PosDef` -/

section PosDefCase

lemma posDef_quad_pos {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef)
    (v : Fin m → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * A i j * v j := by
  let x : Fin m →₀ ℝ := Finsupp.equivFunOnFinite.symm v
  have hx : x ≠ 0 := by
    intro h0; apply hv
    ext i; have := congrFun (congrArg DFunLike.coe h0) i
    simpa [x] using this
  have hpos := hA.2 hx
  have heq : (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj) =
      ∑ i, ∑ j, v i * A i j * v j := by
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Finset.sum_congr rfl fun j _ => by simp [x]
  rwa [heq] at hpos

lemma posSemidef_quad_nonneg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef)
    (v : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * A i j * v j := by
  let x : Fin m →₀ ℝ := Finsupp.equivFunOnFinite.symm v
  have hnn := hA.2 x
  have heq : (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj) =
      ∑ i, ∑ j, v i * A i j * v j := by
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Finset.sum_congr rfl fun j _ => by simp [x]
  rwa [heq] at hnn

lemma posDef_of_symm_quad_pos {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hAsymm : A.IsSymm)
    (hpos : ∀ v : Fin m → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * A i j * v j) :
    A.PosDef := by
  refine ⟨by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hAsymm.eq],
    fun x hx => ?_⟩
  have hv : (x : Fin m → ℝ) ≠ 0 := by
    intro h0; apply hx; ext i; exact congrFun h0 i
  have heq : (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj) =
      ∑ i, ∑ j, x i * A i j * x j := by
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Finset.sum_congr rfl fun j _ => by simp
  rw [heq]
  exact hpos (x : Fin m → ℝ) hv

/-- Weighted sum of characteristic polynomials over `S_m`. -/
noncomputable def weightedCharpoly {m : ℕ} (w : Equiv.Perm (Fin m) → ℝ)
    (A B : Matrix (Fin m) (Fin m) ℝ) : ℝ[X] :=
  ∑ σ : Equiv.Perm (Fin m), C (w σ) * (A * permMat σ * B * (permMat σ)ᵀ).charpoly

lemma weightedCharpoly_monic_deg {m : ℕ} {w : Equiv.Perm (Fin m) → ℝ} (hw : ∑ σ, w σ = 1)
    (A B : Matrix (Fin m) (Fin m) ℝ) :
    (weightedCharpoly w A B).Monic ∧ (weightedCharpoly w A B).natDegree = m := by
  have hdeg_le : (weightedCharpoly w A B).natDegree ≤ m := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    simp only [weightedCharpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have hd : (A * permMat σ * B * (permMat σ)ᵀ).charpoly.natDegree = m := by
      rw [Matrix.charpoly_natDegree_eq_dim]; simp
    have hlt : (A * permMat σ * B * (permMat σ)ᵀ).charpoly.natDegree < j := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  have hcm : (weightedCharpoly w A B).coeff m = 1 := by
    simp only [weightedCharpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    have h1 : ∀ σ, (A * permMat σ * B * (permMat σ)ᵀ).charpoly.coeff m = 1 := by
      intro σ
      have hd : (A * permMat σ * B * (permMat σ)ᵀ).charpoly.natDegree = m := by
        rw [Matrix.charpoly_natDegree_eq_dim]; simp
      have hm := (Matrix.charpoly_monic (A * permMat σ * B * (permMat σ)ᵀ)).coeff_natDegree
      rwa [hd] at hm
    simp_rw [h1, mul_one, hw]
  have hdeg : (weightedCharpoly w A B).natDegree = m :=
    le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero (by rw [hcm]; exact one_ne_zero))
  exact ⟨by rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hcm], hdeg⟩

lemma aeval_charpoly_mul_eq_det {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef)
    (σ : Equiv.Perm (Fin m)) (z : ℂ) :
    Polynomial.aeval z (A * permMat σ * B * (permMat σ)ᵀ).charpoly =
      (A.det : ℂ) * (((permMat σ).map (algebraMap ℝ ℂ))ᵀ * (z • A⁻¹.map (algebraMap ℝ ℂ)) *
        ((permMat σ).map (algebraMap ℝ ℂ)) - B.map (algebraMap ℝ ℂ)).det := by
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA.det_pos.ne'.isUnit
  set M := A * permMat σ * B * (permMat σ)ᵀ
  have h1 : Polynomial.aeval z M.charpoly = (Matrix.scalar (Fin m) z - M.map (algebraMap ℝ ℂ)).det := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map M (algebraMap ℝ ℂ),
      Matrix.eval_charpoly]
  rw [h1]
  set Ac : Matrix (Fin m) (Fin m) ℂ := A.map (algebraMap ℝ ℂ)
  set Aic : Matrix (Fin m) (Fin m) ℂ := A⁻¹.map (algebraMap ℝ ℂ)
  set Bc : Matrix (Fin m) (Fin m) ℂ := B.map (algebraMap ℝ ℂ)
  set Pc : Matrix (Fin m) (Fin m) ℂ := (permMat σ).map (algebraMap ℝ ℂ)
  have hAc_Aic : Ac * Aic = 1 := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) hAinv
    rwa [map_ofReal_mul, map_ofReal_one] at this
  have hPc_orth : Pcᵀ * Pc = 1 := by
    have := congrArg (Matrix.map · (algebraMap ℝ ℂ)) (permMat_orth σ)
    rwa [map_ofReal_mul, map_ofReal_one, Matrix.transpose_map] at this
  have hPc_orth2 : Pc * Pcᵀ = 1 := mul_eq_one_comm.mp hPc_orth
  have hdetPc : Pc.det * Pcᵀ.det = 1 := by rw [← Matrix.det_mul, hPc_orth2, Matrix.det_one]
  have hdetAc : Ac.det = (A.det : ℂ) := by
    simpa [Ac] using (RingHom.map_det (algebraMap ℝ ℂ) A).symm
  have hfac : Matrix.scalar (Fin m) z - M.map (algebraMap ℝ ℂ) =
      Ac * Pc * (Pcᵀ * (z • Aic) * Pc - Bc) * Pcᵀ := by
    have hMmap : M.map (algebraMap ℝ ℂ) = Ac * Pc * Bc * Pcᵀ := by
      simp only [M, Ac, Bc, Pc, map_ofReal_mul, Matrix.transpose_map]
    rw [hMmap, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    have hscalar : Ac * Pc * (Pcᵀ * (z • Aic) * Pc) * Pcᵀ = Matrix.scalar (Fin m) z := by
      calc Ac * Pc * (Pcᵀ * (z • Aic) * Pc) * Pcᵀ
          = z • (Ac * ((Pc * Pcᵀ) * (Aic * (Pc * Pcᵀ)))) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = z • (1 : Matrix (Fin m) (Fin m) ℂ) := by
            rw [hPc_orth2, Matrix.mul_one, Matrix.one_mul, hAc_Aic]
        _ = Matrix.scalar (Fin m) z := by
            ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
    exact hscalar.symm
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hdetAc]
  calc (A.det : ℂ) * Pc.det * (Pcᵀ * (z • Aic) * Pc - Bc).det * Pcᵀ.det
      = (A.det : ℂ) * (Pcᵀ * (z • Aic) * Pc - Bc).det * (Pc.det * Pcᵀ.det) := by ring
    _ = (A.det : ℂ) * (Pcᵀ * (z • Aic) * Pc - Bc).det := by rw [hdetPc, mul_one]

lemma aeval_weightedCharpoly_eq_det_mul_weightedDet {m : ℕ} (w : Equiv.Perm (Fin m) → ℝ)
    {A B : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef) (z : ℂ) :
    Polynomial.aeval z (weightedCharpoly w A B) =
      (A.det : ℂ) * weightedDet w B (z • (A⁻¹.map (algebraMap ℝ ℂ))) := by
  simp only [weightedCharpoly, weightedDet, map_sum, map_mul, Polynomial.aeval_C, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [aeval_charpoly_mul_eq_det hA σ z, Complex.coe_algebraMap]
  ring

lemma isSiegelPos_smul_inv_of_posDef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef)
    {z : ℂ} (hz : 0 < z.im) :
    IsSiegelPos (z • (A⁻¹.map (algebraMap ℝ ℂ))) := by
  have hAinv_pd : A⁻¹.PosDef := hA.inv
  have hAinv_symm : A⁻¹.IsSymm := by
    have h := hAinv_pd.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    simp [Matrix.transpose_apply, Matrix.IsSymm.apply hAinv_symm i j]
  · have hpos := posDef_quad_pos hAinv_pd v hv
    have heq : ∑ i, ∑ j, v i * ((z • A⁻¹.map (algebraMap ℝ ℂ)) i j).im * v j =
        z.im * ∑ i, ∑ j, v i * A⁻¹ i j * v j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Complex.mul_im]
      ring
    rw [heq]
    exact mul_pos hz hpos

lemma realRooted_charpoly_mul_of_posDef {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) (hB : B.IsSymm) (σ : Equiv.Perm (Fin m)) :
    RealRooted (A * permMat σ * B * (permMat σ)ᵀ).charpoly := by
  apply realRooted_of_no_nonreal_root (Matrix.charpoly_monic _).ne_zero
  intro z hz
  rw [aeval_charpoly_mul_eq_det hA σ z]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hA.det_pos.ne')
    (det_sub_real_symm_ne_zero
      (isSiegelPos_conj (isSiegelPos_smul_inv_of_posDef hA hz) (permMat_orth σ)) hB)

/-- Right-multiplying swap distribution (`σ ↦ swapsDist L σ⁻¹`). -/
def swapsDistR {m : ℕ} (L : List (ℝ × Equiv.Perm (Fin m))) (σ : Equiv.Perm (Fin m)) : ℝ :=
  swapsDist L σ⁻¹

lemma swapsDistR_nil {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    swapsDistR ([] : List (ℝ × Equiv.Perm (Fin m))) σ = if σ = 1 then 1 else 0 := by
  simp [swapsDistR, swapsDist, inv_eq_one]

lemma swapsDistR_cons_swap {m : ℕ} (p : ℝ) (i j : Fin m)
    (rest : List (ℝ × Equiv.Perm (Fin m))) (σ : Equiv.Perm (Fin m)) :
    swapsDistR ((p, Equiv.swap i j) :: rest) σ =
      p * swapsDistR rest σ + (1 - p) * swapsDistR rest (σ * Equiv.swap i j) := by
  simp only [swapsDistR, swapsDist, _root_.mul_inv_rev, Equiv.swap_inv]

lemma swapsDistR_sum {m : ℕ} (L : List (ℝ × Equiv.Perm (Fin m))) :
    ∑ σ : Equiv.Perm (Fin m), swapsDistR L σ = 1 := by
  rw [← swapsDist_sum L]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)

lemma swapsDist_weightedDet_stable {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.IsSymm)
    (L : List (ℝ × Equiv.Perm (Fin m)))
    (hL : ∀ x ∈ L, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2) :
    ∀ Z, IsSiegelPos Z → weightedDet (swapsDistR L) B Z ≠ 0 := by
  induction L with
  | nil =>
    intro Z hZ
    have heq : weightedDet (swapsDistR ([] : List (ℝ × Equiv.Perm (Fin m)))) B Z =
        (Z - B.map (algebraMap ℝ ℂ)).det := by
      simp only [weightedDet, swapsDistR_nil]
      rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin m))]
      · simp [permMat_one]
      · intro σ _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [heq]
    exact det_sub_real_symm_ne_zero hZ hB
  | cons x rest ih =>
    rcases x with ⟨p, τ⟩
    obtain ⟨hp, i, j, hij, rfl⟩ := hL (p, τ) List.mem_cons_self
    have hrest : ∀ y ∈ rest, y.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap y.2 :=
      fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hstab_rest := ih hrest
    intro Z hZ
    cases m with
    | zero => exact Fin.elim0 i
    | succ n =>
      obtain ⟨u, hu, hrefl⟩ := reflMat_swap hij
      have hcomb : weightedDet (swapsDistR ((p, Equiv.swap i j) :: rest)) B Z =
          (p : ℂ) * weightedDet (swapsDistR rest) B Z +
            ((1 - p : ℝ) : ℂ) * weightedDet (swapsDistR rest) B
              (((reflMat u).map (algebraMap ℝ ℂ))ᵀ * Z * ((reflMat u).map (algebraMap ℝ ℂ))) := by
        simp only [weightedDet, swapsDistR_cons_swap, Complex.ofReal_add, Complex.ofReal_mul,
          add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
        apply congrArg ((p : ℂ) * _ + ·)
        apply congrArg (((1 - p : ℝ) : ℂ) * ·)
        rw [hrefl]
        refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ fun σ => ?_
        dsimp only [Equiv.mulRight]
        apply congrArg ((swapsDistR rest (σ * Equiv.swap i j) : ℂ) * ·)
        apply congrArg Matrix.det
        apply congrArg (· - B.map (algebraMap ℝ ℂ))
        have hswap : σ * Equiv.swap i j * Equiv.swap i j = σ := by
          rw [mul_assoc, Equiv.swap_mul_self, mul_one]
        have h1 : permMat σ = permMat (Equiv.swap i j) * permMat (σ * Equiv.swap i j) := by
          conv_lhs => rw [← hswap]
          exact permMat_mul _ _
        simp only [h1, map_ofReal_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        rfl
      rw [hcomb]
      exact weightedDet_refl_stable (swapsDistR_sum rest) hstab_rest hu hp hZ

lemma charpoly_perm_conj_swap {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (τ σ : Equiv.Perm (Fin m)) :
    (((permMat τ)ᵀ * A * permMat τ) * permMat σ * B * (permMat σ)ᵀ).charpoly =
      (A * permMat (σ * τ) * B * (permMat (σ * τ))ᵀ).charpoly := by
  have hPτ : permMat τ * (permMat τ)ᵀ = 1 := mul_eq_one_comm.mp (permMat_orth τ)
  have hmul : ((permMat τ)ᵀ * A * permMat τ) * permMat σ * B * (permMat σ)ᵀ =
      (permMat τ)ᵀ * (A * permMat (σ * τ) * B * (permMat (σ * τ))ᵀ) * permMat τ := by
    calc ((permMat τ)ᵀ * A * permMat τ) * permMat σ * B * (permMat σ)ᵀ
        = (permMat τ)ᵀ * (A * (permMat τ * permMat σ) * B * ((permMat σ)ᵀ * ((permMat τ)ᵀ * permMat τ))) := by
          rw [permMat_orth, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (permMat τ)ᵀ * (A * permMat (σ * τ) * B * (permMat (σ * τ))ᵀ) * permMat τ := by
          simp only [permMat_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hmul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hPτ, Matrix.one_mul]

lemma posDef_conj_perm {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef)
    (τ : Equiv.Perm (Fin m)) :
    ((permMat τ)ᵀ * A * permMat τ).PosDef := by
  have hAsymm : A.IsSymm := by
    have h := hA.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  apply posDef_of_symm_quad_pos
  · change ((permMat τ)ᵀ * A * permMat τ)ᵀ = (permMat τ)ᵀ * A * permMat τ
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hAsymm.eq, Matrix.mul_assoc]
  · intro v hv
    have hPv : permMat τ *ᵥ v ≠ 0 := by
      intro h0
      have h1 : ((permMat τ)ᵀ * permMat τ) *ᵥ v = 0 := by
        rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      rw [permMat_orth, Matrix.one_mulVec] at h1
      exact hv h1
    have hpos := posDef_quad_pos hA (permMat τ *ᵥ v) hPv
    have heq : ∑ i, ∑ j, v i * (((permMat τ)ᵀ * A * permMat τ) i j) * v j =
        ∑ k, ∑ l, (permMat τ *ᵥ v) k * A k l * (permMat τ *ᵥ v) l := by
      have hquad : ∀ M : Matrix (Fin m) (Fin m) ℝ, ∀ x : Fin m → ℝ,
          ∑ i, ∑ j, x i * M i j * x j = dotProduct x (M *ᵥ x) := by
        intro M x
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hquad, hquad]
      calc dotProduct v (((permMat τ)ᵀ * A * permMat τ) *ᵥ v)
          = dotProduct v ((permMat τ)ᵀ *ᵥ ((A * permMat τ) *ᵥ v)) := by
            rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
        _ = dotProduct (v ᵥ* (permMat τ)ᵀ) ((A * permMat τ) *ᵥ v) := by
            rw [Matrix.dotProduct_mulVec]
        _ = dotProduct (permMat τ *ᵥ v) (A *ᵥ (permMat τ *ᵥ v)) := by
            rw [Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec]
    rw [heq]; exact hpos

lemma weightedCharpoly_swapsDistR_cons {m : ℕ} (A' B : Matrix (Fin m) (Fin m) ℝ)
    (q : ℝ) (i j : Fin m) (rest : List (ℝ × Equiv.Perm (Fin m))) :
    C q * weightedCharpoly (swapsDistR rest) A' B +
      C (1 - q) * weightedCharpoly (swapsDistR rest)
        ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B =
    weightedCharpoly (swapsDistR ((q, Equiv.swap i j) :: rest)) A' B := by
  unfold weightedCharpoly
  rw [Finset.mul_sum, Finset.mul_sum]
  have hshift :
      ∑ σ : Equiv.Perm (Fin m),
        C (1 - q) * (C (swapsDistR rest σ) *
          (((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) *
            permMat σ * B * (permMat σ)ᵀ).charpoly) =
      ∑ σ : Equiv.Perm (Fin m),
        C (1 - q) * (C (swapsDistR rest (σ * Equiv.swap i j)) *
          (A' * permMat σ * B * (permMat σ)ᵀ).charpoly) := by
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ fun σ => ?_
    have hswap : σ * Equiv.swap i j * Equiv.swap i j = σ := by
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    change C (1 - q) * (C (swapsDistR rest σ) *
        (((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) *
          permMat σ * B * (permMat σ)ᵀ).charpoly) =
      C (1 - q) * (C (swapsDistR rest (σ * Equiv.swap i j * Equiv.swap i j)) *
        (A' * permMat (σ * Equiv.swap i j) * B * (permMat (σ * Equiv.swap i j))ᵀ).charpoly)
    rw [hswap, charpoly_perm_conj_swap A' B (Equiv.swap i j) σ]
  rw [hshift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [swapsDistR_cons_swap, map_add, map_mul, map_mul]
  ring

lemma posDef_swaps_descent_step {m : ℕ} {A' B : Matrix (Fin m) (Fin m) ℝ}
    (hA' : A'.PosDef) (hB : B.IsSymm)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {i j : Fin m} (hij : i ≠ j)
    (rest : List (ℝ × Equiv.Perm (Fin m)))
    (hrest : ∀ y ∈ rest, y.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap y.2)
    (hRR : ∀ (L' : List (ℝ × Equiv.Perm (Fin m))) (M : Matrix (Fin m) (Fin m) ℝ),
      M.PosDef → (∀ x ∈ L', x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2) →
      RealRooted (weightedCharpoly (swapsDistR L') M B))
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (ih1 : ∃ σ : Equiv.Perm (Fin m),
      matrixEig (A' * permMat σ * B * (permMat σ)ᵀ) k ≤
        kthLargestRoot (weightedCharpoly (swapsDistR rest) A' B) k)
    (ih2 : ∃ σ : Equiv.Perm (Fin m),
      matrixEig (((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) *
        permMat σ * B * (permMat σ)ᵀ) k ≤
        kthLargestRoot (weightedCharpoly (swapsDistR rest)
          ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B) k) :
    ∃ σ : Equiv.Perm (Fin m),
      matrixEig (A' * permMat σ * B * (permMat σ)ᵀ) k ≤
        kthLargestRoot (weightedCharpoly (swapsDistR ((p, Equiv.swap i j) :: rest)) A' B) k := by
  have hconv : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      RealRooted (C q * weightedCharpoly (swapsDistR rest) A' B +
        C (1 - q) * weightedCharpoly (swapsDistR rest)
          ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B) := by
    intro q hq
    rw [weightedCharpoly_swapsDistR_cons A' B q i j rest]
    exact hRR ((q, Equiv.swap i j) :: rest) A' hA' fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact ⟨hq, i, j, hij, rfl⟩
      · exact hrest y hmem
  have hmin := kthLargestRoot_convex_le
    (weightedCharpoly_monic_deg (swapsDistR_sum rest) A' B).1
    (weightedCharpoly_monic_deg (swapsDistR_sum rest) A' B).2
    (weightedCharpoly_monic_deg (swapsDistR_sum rest)
      ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B).1
    (weightedCharpoly_monic_deg (swapsDistR_sum rest)
      ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B).2
    hconv hp hk1 hkm
  rw [weightedCharpoly_swapsDistR_cons A' B p i j rest] at hmin
  rcases le_total
      (kthLargestRoot (weightedCharpoly (swapsDistR rest) A' B) k)
      (kthLargestRoot (weightedCharpoly (swapsDistR rest)
        ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B) k) with hle | hle
  · obtain ⟨σ, hσ⟩ := ih1
    have hle' : kthLargestRoot (weightedCharpoly (swapsDistR rest) A' B) k ≤
        kthLargestRoot (weightedCharpoly (swapsDistR ((p, Equiv.swap i j) :: rest)) A' B) k := by
      rw [min_eq_left hle] at hmin; exact hmin
    exact ⟨σ, le_trans hσ hle'⟩
  · obtain ⟨σ, hσ⟩ := ih2
    have hle' : kthLargestRoot (weightedCharpoly (swapsDistR rest)
          ((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) B) k ≤
        kthLargestRoot (weightedCharpoly (swapsDistR ((p, Equiv.swap i j) :: rest)) A' B) k := by
      rw [min_eq_right hle] at hmin; exact hmin
    refine ⟨σ * Equiv.swap i j, ?_⟩
    have heig : matrixEig (A' * permMat (σ * Equiv.swap i j) * B * (permMat (σ * Equiv.swap i j))ᵀ) k =
        matrixEig (((permMat (Equiv.swap i j))ᵀ * A' * permMat (Equiv.swap i j)) *
          permMat σ * B * (permMat σ)ᵀ) k := by
      unfold matrixEig
      rw [charpoly_perm_conj_swap A' B (Equiv.swap i j) σ]
    rw [heig]
    exact le_trans hσ hle'

/-- Binary tree descent on `L` for `A.PosDef` and symmetric `B`. -/
lemma posDef_swaps_descent {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosDef) (hB : B.IsSymm)
    (L : List (ℝ × Equiv.Perm (Fin m)))
    (hL : ∀ x ∈ L, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2) :
    RealRooted (weightedCharpoly (swapsDistR L) A B) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ σ : Equiv.Perm (Fin m),
        matrixEig (A * permMat σ * B * (permMat σ)ᵀ) k ≤
          kthLargestRoot (weightedCharpoly (swapsDistR L) A B) k := by
  have hRR : ∀ (L' : List (ℝ × Equiv.Perm (Fin m))) (A' : Matrix (Fin m) (Fin m) ℝ),
      A'.PosDef → (∀ x ∈ L', x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2) →
      RealRooted (weightedCharpoly (swapsDistR L') A' B) := by
    intro L' A' hA' hL'
    have hm := (weightedCharpoly_monic_deg (swapsDistR_sum L') A' B).1
    apply realRooted_of_no_nonreal_root hm.ne_zero
    intro z hz
    rw [aeval_weightedCharpoly_eq_det_mul_weightedDet _ hA' z]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hA'.det_pos.ne')
      (swapsDist_weightedDet_stable hB L' hL' _ (isSiegelPos_smul_inv_of_posDef hA' hz))
  refine ⟨hRR L A hA hL, fun k hk1 hkm => ?_⟩
  suffices ∀ (L' : List (ℝ × Equiv.Perm (Fin m)))
      (hL' : ∀ x ∈ L', x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap x.2)
      (A' : Matrix (Fin m) (Fin m) ℝ) (hA' : A'.PosDef),
      ∃ σ : Equiv.Perm (Fin m),
        matrixEig (A' * permMat σ * B * (permMat σ)ᵀ) k ≤
          kthLargestRoot (weightedCharpoly (swapsDistR L') A' B) k from
    this L hL A hA
  intro L'
  induction L' with
  | nil =>
    intro _ A' _
    refine ⟨1, ?_⟩
    have heq : weightedCharpoly (swapsDistR ([] : List (ℝ × Equiv.Perm (Fin m)))) A' B =
        (A' * permMat (1 : Equiv.Perm (Fin m)) * B * (permMat (1 : Equiv.Perm (Fin m)))ᵀ).charpoly := by
      simp only [weightedCharpoly, swapsDistR_nil]
      rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin m))]
      · simp
      · intro σ _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [heq]; exact le_rfl
  | cons x rest ih =>
    intro hL' A' hA'
    rcases x with ⟨p, τ⟩
    obtain ⟨hp, i, j, hij, rfl⟩ := hL' (p, τ) List.mem_cons_self
    have hrest : ∀ y ∈ rest, y.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsSwap y.2 :=
      fun y hy => hL' y (List.mem_cons_of_mem _ hy)
    exact posDef_swaps_descent_step hA' hB hp hij rest hrest hRR hk1 hkm
      (ih hrest A' hA')
      (ih hrest _ (posDef_conj_perm hA' (Equiv.swap i j)))

end PosDefCase

/-! ### Section 5: Passing from `PosDef` to `PosSemidef` and Symmetry -/

section MainProof

lemma expCharpolyMul_eq_weightedCharpoly_unif {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    expCharpolyMul A B =
      weightedCharpoly (fun _ => (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) A B := by
  simp only [expCharpolyMul, permAvg, weightedCharpoly, Finset.smul_sum, Polynomial.smul_eq_C_mul]

lemma charpoly_mul_perm_symm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (σ : Equiv.Perm (Fin m)) :
    (A * permMat σ * B * (permMat σ)ᵀ).charpoly =
      (B * (permMat σ)ᵀ * A * permMat σ).charpoly := by
  calc (A * permMat σ * B * (permMat σ)ᵀ).charpoly
      = (A * (permMat σ * B * (permMat σ)ᵀ)).charpoly := by simp only [Matrix.mul_assoc]
    _ = ((permMat σ * B * (permMat σ)ᵀ) * A).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (permMat σ * (B * (permMat σ)ᵀ * A)).charpoly := by simp only [Matrix.mul_assoc]
    _ = ((B * (permMat σ)ᵀ * A) * permMat σ).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (B * (permMat σ)ᵀ * A * permMat σ).charpoly := by simp only [Matrix.mul_assoc]

lemma expCharpolyMul_comm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    expCharpolyMul A B = expCharpolyMul B A := by
  simp only [expCharpolyMul, permAvg]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin m))) _ _ fun σ => ?_
  simp only [Equiv.inv_apply, ← permMat_transpose, Matrix.transpose_transpose]
  exact charpoly_mul_perm_symm A B σ

lemma tendsto_coeff_charpoly_add_inv {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (σ : Equiv.Perm (Fin m)) (j : ℕ) :
    Tendsto (fun n : ℕ =>
      ((A + ((n : ℝ) + 1)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) * permMat σ * B * (permMat σ)ᵀ).charpoly.coeff j)
      atTop (nhds ((A * permMat σ * B * (permMat σ)ᵀ).charpoly.coeff j)) := by
  let f : ℝ → Matrix (Fin m) (Fin m) ℝ := fun t => (A + t • 1) * permMat σ * B * (permMat σ)ᵀ
  have hpoly : ∀ t, (f t).charpoly.coeff j =
      ∑ τ : Equiv.Perm (Fin m), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        (∏ i : Fin m, (Matrix.scalar (Fin m) (X : ℝ[X]) - (f t).map C) (τ i) i).coeff j := by
    intro t
    rw [Matrix.charpoly, Matrix.charmatrix, Matrix.det_apply, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, show ((Equiv.Perm.sign τ : ℤ) : ℝ[X]) =
      C ((Equiv.Perm.sign τ : ℤ) : ℝ) by simp, Polynomial.coeff_C_mul]
    rfl
  have hcont : Continuous (fun t : ℝ => (f t).charpoly.coeff j) := by
    simp_rw [hpoly]
    refine continuous_finsetSum _ fun τ _ => continuous_const.mul ?_
    suffices ∀ (s : Finset (Fin m)) (k : ℕ),
        Continuous (fun t : ℝ => (∏ i ∈ s, (Matrix.scalar (Fin m) (X : ℝ[X]) - (f t).map C) (τ i) i).coeff k) from
      this Finset.univ j
    intro s
    induction s using Finset.induction_on with
    | empty => intro k; simp only [Finset.prod_empty]; exact continuous_const
    | @insert a s ha ih =>
      intro k
      simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
      refine continuous_finsetSum _ fun kl _ => Continuous.mul ?_ (ih kl.2)
      have hentry : Continuous (fun t : ℝ => f t (τ a) a) := by
        simp only [f, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        refine continuous_finsetSum _ fun _ _ => Continuous.mul ?_ continuous_const
        refine continuous_finsetSum _ fun _ _ => Continuous.mul ?_ continuous_const
        refine continuous_finsetSum _ fun _ _ => Continuous.mul ?_ continuous_const
        exact continuous_const.add (continuous_id.mul continuous_const)
      by_cases h0 : kl.1 = 0
      · simp only [h0, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
          Matrix.map_apply, Polynomial.coeff_sub, Polynomial.coeff_C_zero]
        by_cases hτ : τ a = a
        · simp only [hτ, if_true, Polynomial.coeff_X_zero, zero_sub]
          have hentry' : Continuous (fun t : ℝ => f t a a) := by simpa [hτ] using hentry
          exact hentry'.neg
        · simp only [hτ, if_false, Polynomial.coeff_zero, zero_sub]
          exact hentry.neg
      · by_cases h1 : kl.1 = 1
        · simp only [h1, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
            Matrix.map_apply, Polynomial.coeff_sub, Polynomial.coeff_C_of_ne_zero one_ne_zero, sub_zero]
          exact continuous_const
        · simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
            Matrix.map_apply, Polynomial.coeff_sub, Polynomial.coeff_C_of_ne_zero h0, sub_zero]
          exact continuous_const
  have htend0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun n : ℕ => (f (((n : ℝ) + 1)⁻¹)).charpoly.coeff j) atTop
      (nhds ((f 0).charpoly.coeff j)) := (hcont.tendsto 0).comp htend0
  simpa [f] using hlim

lemma lemma_2_2_of_posSemidef_left {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hB : B.IsSymm) :
    RealRooted (expCharpolyMul A B) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ σ : Equiv.Perm (Fin m),
        RealRooted (A * permMat σ * B * (permMat σ)ᵀ).charpoly ∧
          matrixEig (A * permMat σ * B * (permMat σ)ᵀ) k ≤
            kthLargestRoot (expCharpolyMul A B) k := by
  obtain ⟨L, hL_valid, hL_unif⟩ := exists_uniform_swaps m
  have hexp_eq : ∀ M : Matrix (Fin m) (Fin m) ℝ,
      expCharpolyMul M B = weightedCharpoly (swapsDistR L) M B := by
    intro M
    rw [expCharpolyMul_eq_weightedCharpoly_unif]
    simp only [weightedCharpoly, swapsDistR]
    refine Finset.sum_congr rfl fun σ _ => by rw [hL_unif σ⁻¹]
  let An : ℕ → Matrix (Fin m) (Fin m) ℝ := fun n => A + ((n : ℝ) + 1)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hAsymm : A.IsSymm := by
    have h := hA.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hAn_pd : ∀ n, (An n).PosDef := by
    intro n
    apply posDef_of_symm_quad_pos (hAsymm.add (by ext i j; simp [Matrix.one_apply, eq_comm]))
    intro v hv
    have h1 := posSemidef_quad_nonneg hA v
    have h2 : 0 < ∑ i, v i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun j _ => sq_nonneg (v j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have heq : ∑ i, ∑ j, v i * (An n i j) * v j =
        (∑ i, ∑ j, v i * A i j * v j) + ((n : ℝ) + 1)⁻¹ * (∑ i, v i ^ 2) := by
      simp only [An, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_add, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      trans ∑ j : Fin m, if i = j then ((n : ℝ) + 1)⁻¹ * v i ^ 2 else 0
      · refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j
        · subst hij; simp; ring
        · simp [hij]
      · simp
    rw [heq]; nlinarith
  have hAn_res : ∀ n, RealRooted (expCharpolyMul (An n) B) ∧
      ∀ k, 1 ≤ k → k ≤ m → ∃ σ : Equiv.Perm (Fin m),
        matrixEig (An n * permMat σ * B * (permMat σ)ᵀ) k ≤
          kthLargestRoot (expCharpolyMul (An n) B) k := fun n => by
    rw [hexp_eq (An n)]
    exact posDef_swaps_descent (hAn_pd n) hB L hL_valid
  have hAn_md : ∀ n, (expCharpolyMul (An n) B).Monic ∧ (expCharpolyMul (An n) B).natDegree = m := by
    intro n; rw [hexp_eq]; exact weightedCharpoly_monic_deg (swapsDistR_sum L) (An n) B
  have hA_md : (expCharpolyMul A B).Monic ∧ (expCharpolyMul A B).natDegree = m := by
    rw [hexp_eq]; exact weightedCharpoly_monic_deg (swapsDistR_sum L) A B
  have hcoeff_tend : ∀ j, Tendsto (fun n => (expCharpolyMul (An n) B).coeff j) atTop
      (nhds ((expCharpolyMul A B).coeff j)) := by
    intro j
    simp only [expCharpolyMul_eq_weightedCharpoly_unif, weightedCharpoly,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    refine tendsto_finsetSum _ fun σ _ => tendsto_const_nhds.mul ?_
    exact tendsto_coeff_charpoly_add_inv A B σ j
  have hlim := tendsto_realRooted_and_kthLargestRoot
    (fun n => (hAn_md n).1) (fun n => (hAn_md n).2) (fun n => (hAn_res n).1)
    hA_md.1 hA_md.2 hcoeff_tend
  refine ⟨hlim.1, fun k hk1 hkm => ?_⟩
  choose σn hσn using fun n => (hAn_res n).2 k hk1 hkm
  obtain ⟨σ, hinf⟩ : ∃ σ : Equiv.Perm (Fin m), Set.Infinite {n : ℕ | σn n = σ} := by
    by_contra hall
    push Not at hall
    have hfin : (Set.univ : Set ℕ).Finite := by
      have hunion : (Set.univ : Set ℕ) = ⋃ σ : Equiv.Perm (Fin m), {n : ℕ | σn n = σ} := by
        ext n; simp
      rw [hunion]
      exact Set.finite_iUnion hall
    exact Set.infinite_univ hfin
  have hex : ∀ N : ℕ, ∃ n ≥ N, σn n = σ := fun N => by
    by_contra hnone
    push Not at hnone
    apply hinf
    exact (Set.finite_lt_nat N).subset fun n hn => by
      by_contra hge; exact hnone n (not_lt.mp hge) hn
  let φ : ℕ → ℕ := Nat.rec (Classical.choose (hex 0)) (fun _ prev => Classical.choose (hex (prev + 1)))
  have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ fun n => by
    have h1 : φ n + 1 ≤ Classical.choose (hex (φ n + 1)) := (Classical.choose_spec (hex (φ n + 1))).1
    change φ n < Classical.choose (hex (φ n + 1))
    omega
  have hφ_eq : ∀ n, σn (φ n) = σ := fun n => by
    cases n with
    | zero => exact (Classical.choose_spec (hex 0)).2
    | succ n => exact (Classical.choose_spec (hex (φ n + 1))).2
  have hlim_lhs_full := tendsto_realRooted_and_kthLargestRoot (m := m)
    (fun n => Matrix.charpoly_monic (An (φ n) * permMat σ * B * (permMat σ)ᵀ))
    (fun n => by rw [Matrix.charpoly_natDegree_eq_dim]; exact Fintype.card_fin m)
    (fun n => realRooted_charpoly_mul_of_posDef (hAn_pd (φ n)) hB σ)
    (Matrix.charpoly_monic (A * permMat σ * B * (permMat σ)ᵀ))
    (by rw [Matrix.charpoly_natDegree_eq_dim]; exact Fintype.card_fin m)
    (fun j => (tendsto_coeff_charpoly_add_inv A B σ j).comp hφ_mono.tendsto_atTop)
  refine ⟨σ, hlim_lhs_full.1, ?_⟩
  have hlim_rhs : Tendsto (fun n => kthLargestRoot (expCharpolyMul (An (φ n)) B) k) atTop
      (nhds (kthLargestRoot (expCharpolyMul A B) k)) :=
    (hlim.2 k hk1 hkm).comp hφ_mono.tendsto_atTop
  exact le_of_tendsto_of_tendsto (hlim_lhs_full.2 k hk1 hkm) hlim_rhs
    (Eventually.of_forall fun n => by
      have := hσn (φ n)
      rwa [hφ_eq n] at this)

theorem lemma_2_2_aux {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (hpsd : A.PosSemidef ∨ B.PosSemidef) :
    RealRooted (expCharpolyMul A B) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ σ : Equiv.Perm (Fin m),
        RealRooted (A * permMat σ * B * (permMat σ).transpose).charpoly ∧
          matrixEig (A * permMat σ * B * (permMat σ).transpose) k ≤
            kthLargestRoot (expCharpolyMul A B) k := by
  rcases hpsd with hApsd | hBpsd
  · exact lemma_2_2_of_posSemidef_left hApsd hB
  · obtain ⟨hrr, hex⟩ := lemma_2_2_of_posSemidef_left hBpsd hA
    rw [expCharpolyMul_comm B A] at hrr
    refine ⟨hrr, fun k hk1 hkm => ?_⟩
    obtain ⟨σ, hσ_rr, hσ_le⟩ := hex k hk1 hkm
    rw [expCharpolyMul_comm B A] at hσ_le
    refine ⟨σ⁻¹, ?_, ?_⟩
    · have hcp : (A * permMat σ⁻¹ * B * (permMat σ⁻¹)ᵀ).charpoly =
          (B * permMat σ * A * (permMat σ)ᵀ).charpoly := by
        rw [← permMat_transpose, Matrix.transpose_transpose]
        exact (charpoly_mul_perm_symm B A σ).symm
      rwa [hcp]
    · have hcp : (A * permMat σ⁻¹ * B * (permMat σ⁻¹)ᵀ).charpoly =
          (B * permMat σ * A * (permMat σ)ᵀ).charpoly := by
        rw [← permMat_transpose, Matrix.transpose_transpose]
        exact (charpoly_mul_perm_symm B A σ).symm
      rwa [matrixEig, hcp]

end MainProof

end SuperRamanujan227.Main

open SuperRamanujan227.Main in
theorem solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (hpsd : A.PosSemidef ∨ B.PosSemidef) :
    RealRooted (expCharpolyMul A B) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ σ : Equiv.Perm (Fin m),
        RealRooted (A * permMat σ * B * (permMat σ).transpose).charpoly ∧
          matrixEig (A * permMat σ * B * (permMat σ).transpose) k ≤
            kthLargestRoot (expCharpolyMul A B) k :=
  lemma_2_2_aux A B hA hB hpsd
