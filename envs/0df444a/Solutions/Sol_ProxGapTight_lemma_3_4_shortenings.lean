-- Prove2me | solution 1 for ProxGapTight.lemma_3_4_shortenings
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:13:24.313211+00:00
-- url     : https://prove2.me/submissions/0b016b66-952b-4bb8-9c6d-7c9ae3395a04

import Mathlib
import Definitions.Def_ProxGapTight_Um
import Definitions.Def_ProxGapTight_shorten
import Definitions.Def_ProxGapTight_minDist
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_Lm
import Theorems.Thm_ProxGapTight_theorem_3_3_small_weight

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Shorten
open ProxGapTight

open ProxGapTight

theorem arith_facts (Q m : ℕ) (hQ : 33 ≤ Q) (hm : 4 ≤ m) :
    ∃ g M : ℕ, g = (Q ^ (m - 3) - 1) / (Q - 1) ∧ 1 ≤ M ∧ Q ^ (m - 3) = Q * M ∧
      em Q m = Q * M + g ∧ Lm Q m + 3 * M + 1 = 3 * (Q * M) ∧ M ≤ g ∧ 32 * g + 1 ≤ 33 * M := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
  have h1 : n + 4 - 3 = n + 1 := by omega
  have h2 : n + 4 - 4 = n := by omega
  have h3 : n + 4 - 2 = n + 2 := by omega
  set M := Q ^ n with hM
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hN : Q ^ (n + 1) = Q * M := by rw [pow_succ]; ring
  have hN2 : Q ^ (n + 2) = Q * (Q * M) := by rw [pow_succ, hN]; ring
  have hQM : 33 * M ≤ Q * M := Nat.mul_le_mul_right _ hQ
  have hQQM : 33 * (Q * M) ≤ Q * (Q * M) := Nat.mul_le_mul_right _ hQ
  have hdvd1 : Q - 1 ∣ Q ^ (n + 1) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow Q 1 (n + 1)
  have hdvd2 : Q - 1 ∣ Q ^ (n + 2) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow Q 1 (n + 2)
  obtain ⟨g, hg⟩ := hdvd1
  obtain ⟨e, he⟩ := hdvd2
  have hQ1 : 0 < Q - 1 := by omega
  have hgdef : (Q ^ (n + 1) - 1) / (Q - 1) = g := by
    rw [hg]; exact Nat.mul_div_cancel_left _ hQ1
  have hedef : (Q ^ (n + 2) - 1) / (Q - 1) = e := by
    rw [he]; exact Nat.mul_div_cancel_left _ hQ1
  -- (Q-1) * g = Q*M - 1
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hg he hQ1 hgdef hedef
  have hg' : Q' * g + 1 = (Q' + 1) * M := by
    rw [hN] at hg; have : 1 ≤ (Q' + 1) * M := Nat.mul_pos (by omega) hM1; omega
  have he' : Q' * e + 1 = (Q' + 1) * ((Q' + 1) * M) := by
    rw [hN2] at he; have : 1 ≤ (Q' + 1) * ((Q' + 1) * M) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hM1); omega
  -- e = Q*M + g
  have hQ' : 32 ≤ Q' := by omega
  have hgM : M ≤ g := by
    by_contra h
    push Not at h
    nlinarith
  have hg32 : 32 * g + 1 ≤ 33 * M := by
    have : Q' * (g - M) + 1 = M := by
      have : Q' * g = Q' * M + Q' * (g - M) := by
        rw [← Nat.mul_add]; congr 1; omega
      nlinarith
    have h32 : 32 * (g - M) ≤ Q' * (g - M) := Nat.mul_le_mul_right _ hQ'
    omega
  have heq : e = (Q' + 1) * M + g := by
    have : Q' * e + 1 = Q' * ((Q' + 1) * M + g) + 1 := by
      rw [he']
      nlinarith
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < Q') (by omega : Q' * e = Q' * ((Q' + 1) * M + g))
    exact this
  refine ⟨g, M, ?_, hM1, ?_, ?_, ?_, hgM, hg32⟩
  · rw [h1]; simp only [Nat.add_sub_cancel]; exact hgdef.symm
  · rw [h1]; exact hN
  · unfold em; rw [h3]; simp only [Nat.add_sub_cancel]; rw [hedef, heq]
  · unfold Lm; rw [h1, h2, hN]; omega



theorem hammingNorm_eq {ι F : Type} [Fintype ι] [Zero F] [DecidableEq F] (c : ι → F) :
    hammingNorm c = (Finset.univ.filter (fun i => c i ≠ 0)).card := rfl


/-- a nonzero linear functional on a finite space over a finite field has kernel of index `q` -/
theorem lin_cnt {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]
    (f : W →ₗ[F] F) (hf : f ≠ 0) :
    Nat.card W = Fintype.card F * Nat.card (LinearMap.ker f) := by
  haveI : FiniteDimensional F W := Module.Finite.of_finite
  have hrange : LinearMap.range f = ⊤ := by
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra h; push Not at h; exact hf (LinearMap.ext h)
    rw [eq_top_iff]
    intro x _
    exact ⟨(x / f w) • w, by simp [hw]⟩
  have h1 : Module.finrank F (LinearMap.range f) = 1 := by
    rw [hrange]; simp
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [h1] at h2
  rw [Module.natCard_eq_pow_finrank (K := F) (V := W),
    Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker f), ← h2, pow_add, pow_one,
    Nat.card_eq_fintype_card]


theorem wt_sum (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Submodule (ZMod p) (ι → ZMod p)) [Fintype M]
    [DecidablePred (fun i => ∃ c ∈ M, c i ≠ 0)] :
    p * (∑ c : M, hammingNorm (c : ι → ZMod p)) =
      (Finset.univ.filter (fun i => ∃ c ∈ M, c i ≠ 0)).card * (p - 1) * Nat.card M := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h1 : (∑ c : M, hammingNorm (c : ι → ZMod p)) =
      ∑ i, (Finset.univ.filter (fun c : M => (c : ι → ZMod p) i ≠ 0)).card := by
    simp only [hammingNorm, Finset.card_filter]
    exact Finset.sum_comm
  rw [h1, Finset.mul_sum]
  have h2 : ∀ i, p * (Finset.univ.filter (fun c : M => (c : ι → ZMod p) i ≠ 0)).card =
      if (∃ c ∈ M, c i ≠ 0) then (p - 1) * Nat.card M else 0 := by
    intro i
    split_ifs with hi
    · let π : M →ₗ[ZMod p] ZMod p := (LinearMap.proj i).comp M.subtype
      have hπ : π ≠ 0 := by
        obtain ⟨c, hc, hci⟩ := hi
        intro h
        exact hci (by simpa [π] using LinearMap.congr_fun h ⟨c, hc⟩)
      have h3 := lin_cnt π hπ
      rw [hcard] at h3
      have h4 : Nat.card (LinearMap.ker π) =
          (Finset.univ.filter (fun c : M => (c : ι → ZMod p) i = 0)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext c
        simp [π, LinearMap.mem_ker]
      have h5 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset M))
        (fun c : M => (c : ι → ZMod p) i ≠ 0)
      simp only [not_not, Finset.card_univ] at h5
      rw [← Nat.card_eq_fintype_card] at h5
      rw [h4] at h3
      have : Nat.card M = _ + _ := h5.symm
      -- Nat.card M = p * k, A + k = Nat.card M
      set A := (Finset.univ.filter (fun c : M => (c : ι → ZMod p) i ≠ 0)).card
      set k := (Finset.univ.filter (fun c : M => (c : ι → ZMod p) i = 0)).card
      have hA : A = (p - 1) * k := by
        have : A + k = p * k := by rw [← h3]; exact h5
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        nlinarith
      rw [hA, h3]; ring
    · have : (Finset.univ.filter (fun c : M => (c : ι → ZMod p) i ≠ 0)) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_not]
        by_contra h
        exact hi ⟨c, c.2, h⟩
      simp [this]
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
  rw [mul_assoc]



theorem core_num (p n Mc S : ℕ) (hp : 2 ≤ p) (hM : 1 ≤ Mc) (h1 : p * S = n * (p - 1) * Mc)
    (h2 : S ≤ 2 * (Mc - 1)) : n ≤ 3 ∧ (n = 3 → p = 2 ∧ 4 ≤ Mc) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨M', rfl⟩ : ∃ M', Mc = M' + 1 := ⟨Mc - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  have hp' : 1 ≤ p' := by omega
  have key : n * p' * (M' + 1) ≤ 2 * (p' + 1) * M' := by
    have : (p' + 1) * S ≤ (p' + 1) * (2 * M') := Nat.mul_le_mul_left _ h2
    nlinarith
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have h4 : 4 * p' * (M' + 1) ≤ n * p' * (M' + 1) := by
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
    have h5 : M' ≤ p' * M' := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  · intro hn
    subst hn
    have hp2 : p' = 1 := by
      by_contra h
      have : 2 ≤ p' := by omega
      nlinarith
    subst hp2
    refine ⟨rfl, ?_⟩
    nlinarith


theorem exists_two_cover {ι : Type} [DecidableEq ι] [Nonempty ι] (I : Finset ι) (h : I.card ≤ 2) :
    ∃ i j, ∀ k ∈ I, k = i ∨ k = j := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  interval_cases hc : I.card
  · rw [Finset.card_eq_zero] at hc
    exact ⟨a, a, by simp [hc]⟩
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    exact ⟨x, x, by simp [hx]⟩
  · obtain ⟨x, y, _, hx⟩ := Finset.card_eq_two.mp hc
    exact ⟨x, y, by simp [hx]⟩

theorem sum_le_aux {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Submodule (ZMod p) (ι → ZMod p)) [Fintype M]
    (hw : ∀ c ∈ M, hammingNorm c ≤ 2) (c0 : M) (hc0 : c0 ≠ 0) :
    (∑ c : M, hammingNorm (c : ι → ZMod p)) ≤
      hammingNorm (c0 : ι → ZMod p) + 2 * (Fintype.card M - 2) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
  have h0 : (0 : M) ∈ (Finset.univ.erase c0) := by
    simp [Finset.mem_erase, hc0.symm]
  rw [← Finset.add_sum_erase _ _ h0]
  have : hammingNorm ((0 : M) : ι → ZMod p) = 0 := by simp
  rw [this, zero_add]
  have hle : ∑ c ∈ (Finset.univ.erase c0).erase 0, hammingNorm (c : ι → ZMod p) ≤
      ∑ c ∈ (Finset.univ.erase c0).erase 0, 2 :=
    Finset.sum_le_sum (fun c _ => hw c c.2)
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0, Finset.card_erase_of_mem
    (Finset.mem_univ c0), Finset.card_univ] at hle
  have : Fintype.card M - 1 - 1 = Fintype.card M - 2 := by omega
  omega

theorem zmod2_ne_zero : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide

theorem core (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule (ZMod p) (ι → ZMod p)) (hw : ∀ c ∈ M, hammingNorm c ≤ 2) :
    Module.finrank (ZMod p) M ≤ 2 ∧
      ((∃ i j : ι, ∀ c ∈ M, ∀ k, k ≠ i → k ≠ j → c k = 0) ∨
        (p = 2 ∧ ∃ x y z : ι, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
          (Pi.single x (1 : ZMod p) + Pi.single y 1 ∈ M) ∧
          (Pi.single y (1 : ZMod p) + Pi.single z 1 ∈ M) ∧
          (Pi.single z (1 : ZMod p) + Pi.single x 1 ∈ M))) := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set I := Finset.univ.filter (fun i => ∃ c ∈ M, c i ≠ 0) with hI
  have hout : ∀ c ∈ M, ∀ k, k ∉ I → c k = 0 := by
    intro c hc k hk
    by_contra h
    exact hk (by simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨c, hc, h⟩)
  have hM1 : 1 ≤ Nat.card M := Nat.card_pos
  have hsum := wt_sum p M
  have hS : (∑ c : M, hammingNorm (c : ι → ZMod p)) ≤ 2 * (Nat.card M - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : M))]
    have h0 : hammingNorm (((0 : M)) : ι → ZMod p) = 0 := by simp
    rw [h0, zero_add]
    have hle : ∑ c ∈ Finset.univ.erase (0 : M), hammingNorm (c : ι → ZMod p) ≤
        ∑ c ∈ Finset.univ.erase (0 : M), 2 := Finset.sum_le_sum (fun c _ => hw c c.2)
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
    omega
  obtain ⟨hn3, hn3'⟩ := core_num p I.card (Nat.card M) _ hp hM1 hsum hS
  -- restriction to I
  let r : M →ₗ[ZMod p] (I → ZMod p) :=
    LinearMap.pi (fun i : I => (LinearMap.proj (i : ι)).comp M.subtype)
  have hr : Function.Injective r := by
    intro a b hab
    apply Subtype.ext
    funext k
    by_cases hk : k ∈ I
    · exact congrFun hab ⟨k, hk⟩
    · rw [hout a a.2 k hk, hout b b.2 k hk]
  have hfin : Module.finrank (ZMod p) M ≤ I.card := by
    have := LinearMap.finrank_le_finrank_of_injective hr
    simpa using this
  by_cases hn2 : I.card ≤ 2
  · refine ⟨hfin.trans hn2, Or.inl ?_⟩
    obtain ⟨i, j, hij⟩ := exists_two_cover I hn2
    refine ⟨i, j, ?_⟩
    intro c hc k hki hkj
    apply hout c hc k
    intro hk
    rcases hij k hk with h | h
    exacts [hki h, hkj h]
  · have hn : I.card = 3 := by omega
    obtain ⟨hp2, hM4⟩ := hn3' hn
    subst hp2
    have hfin2 : Module.finrank (ZMod 2) M ≤ 2 := by
      by_contra hcon
      have h3 : Module.finrank (ZMod 2) M = I.card := by omega
      have hsurj : Function.Surjective r := by
        rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
        · exact hr
        · simpa using h3
      obtain ⟨c, hc⟩ := hsurj (fun _ => 1)
      have hci : ∀ i ∈ I, (c : ι → ZMod 2) i = 1 := by
        intro i hi
        exact congrFun hc ⟨i, hi⟩
      have h1 : I.card ≤ hammingNorm (c : ι → ZMod 2) := by
        rw [hammingNorm_eq]
        apply Finset.card_le_card
        intro i hi
        simp [hci i hi]
      have := hw c c.2
      omega
    have hMc : Nat.card M = 4 := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
      rw [Nat.card_zmod] at h
      have : 2 ^ Module.finrank (ZMod 2) M ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hfin2
      omega
    have hS6 : (∑ c : M, hammingNorm (c : ι → ZMod 2)) = 6 := by
      rw [← hI, hn, hMc] at hsum
      omega
    have hnz : ∀ c ∈ M, c ≠ 0 → hammingNorm c = 2 := by
      intro c hc hc0
      have h := sum_le_aux M hw ⟨c, hc⟩ (by simpa using hc0)
      rw [hS6, ← Nat.card_eq_fintype_card, hMc] at h
      have := hw c hc
      simp only at h
      omega
    refine ⟨hfin2, Or.inr ⟨rfl, ?_⟩⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, hI3⟩ := Finset.card_eq_three.mp hn
    have h01 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := zmod2_ne_zero
    set N : Finset M := Finset.univ.filter (fun c : M => c ≠ 0) with hN
    have hNc : N.card = 3 := by
      have : N = Finset.univ.erase 0 := by
        ext c; simp [hN]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hMc]
    let Φ : ∀ c ∈ N, Finset ι := fun c _ => Finset.univ.filter (fun i => (c : ι → ZMod 2) i ≠ 0)
    have hmaps : ∀ c (hc : c ∈ N), Φ c hc ∈ I.powersetCard 2 := by
      intro c hc
      have hc0 : c ≠ 0 := by simpa [hN] using hc
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨c, c.2, hi⟩
      · have := hnz c c.2 (by simpa using hc0)
        rw [hammingNorm_eq] at this
        exact this
    have hinj : ∀ a b (ha : a ∈ N) (hb : b ∈ N), Φ a ha = Φ b hb → a = b := by
      intro a b ha hb hab
      apply Subtype.ext
      funext i
      have hi := Finset.ext_iff.mp hab i
      simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases h : (a : ι → ZMod 2) i = 0
      · have : (b : ι → ZMod 2) i = 0 := by
          by_contra hb'
          exact hi.mpr hb' h
        rw [h, this]
      · have hb' : (b : ι → ZMod 2) i ≠ 0 := hi.mp h
        rw [h01 _ h, h01 _ hb']
    have hcardt : (I.powersetCard 2).card ≤ N.card := by
      rw [Finset.card_powersetCard, hn, hNc]; decide
    have hsurj := Finset.surj_on_of_inj_on_of_card_le Φ hmaps hinj hcardt
    have key : ∀ a b, a ∈ I → b ∈ I → a ≠ b →
        (Pi.single a (1 : ZMod 2) + Pi.single b 1 : ι → ZMod 2) ∈ M := by
      intro a b ha hb hab
      have hmem : ({a, b} : Finset ι) ∈ I.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair hab⟩
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
      obtain ⟨c, hc, hΦ⟩ := hsurj _ hmem
      have : (c : ι → ZMod 2) = Pi.single a 1 + Pi.single b 1 := by
        funext i
        have hi := Finset.ext_iff.mp hΦ i
        simp only [Φ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton] at hi
        by_cases hia : i = a
        · subst hia
          have := hi.mp (Or.inl rfl)
          simp [Pi.single_apply, hab, h01 _ this]
        · by_cases hib : i = b
          · subst hib
            have := hi.mp (Or.inr rfl)
            simp [Pi.single_apply, hab.symm, h01 _ this]
          · have : (c : ι → ZMod 2) i = 0 := by
              by_contra h
              rcases hi.mpr h with h' | h'
              exacts [hia h', hib h']
            simp [this, Pi.single_apply, hia, hib]
      rw [← this]
      exact c.2
    have hxI : x ∈ I := by rw [hI3]; simp
    have hyI : y ∈ I := by rw [hI3]; simp
    have hzI : z ∈ I := by rw [hI3]; simp
    exact ⟨x, y, z, hxy, hxz, hyz, key x y hxI hyI hxy, key y z hyI hzI hyz, key z x hzI hxI hxz.symm⟩




variable {L ι F : Type} [Fintype L] [Fintype ι] [DecidableEq L] [DecidableEq ι] [Field F]
  [DecidableEq F]

/-- indicator vectors of the sets `A i` -/
def ind (A : ι → Finset L) (i : ι) : L → F := fun ℓ => if ℓ ∈ A i then 1 else 0

/-- linear combination map -/
def lc (A : ι → Finset L) : (ι → F) →ₗ[F] (L → F) :=
  Fintype.linearCombination F (ind A : ι → L → F)

theorem lc_apply (A : ι → Finset L) (c : ι → F) (ℓ : L) :
    lc A c ℓ = ∑ i, c i * (if ℓ ∈ A i then 1 else 0) := by
  simp [lc, Fintype.linearCombination_apply, ind]

theorem lc_single (A : ι → Finset L) (i : ι) (a : F) :
    lc A (Pi.single i a) = a • (ind A i : L → F) := by
  simp [lc, Fintype.linearCombination_apply_single]

theorem hammingNorm_le_of_subset (c : ι → F) (T : Finset ι) (h : ∀ i, c i ≠ 0 → i ∈ T) :
    hammingNorm c ≤ T.card := by
  rw [hammingNorm_eq]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact h i hi

section geo
variable (A : ι → Finset L) (e g : ℕ)

theorem indep8 (hcard : ∀ i, (A i).card = e) (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g)
    (h7 : 7 * g < e) (c : ι → F) (hc : hammingNorm c ≤ 8) (h0 : lc A c = 0) : c = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set T := Finset.univ.filter (fun i => c i ≠ 0) with hT
  have hTc : T.card ≤ 8 := hc
  have hiT : i ∈ T := by simp [hT, hi]
  have hbig : ((T.erase i).biUnion (fun j => A i ∩ A j)).card ≤ 7 * g := by
    calc _ ≤ ∑ j ∈ T.erase i, (A i ∩ A j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ T.erase i, g := Finset.sum_le_sum (fun j hj => hinter i j (Finset.ne_of_mem_erase hj).symm)
      _ = (T.erase i).card * g := by simp
      _ ≤ 7 * g := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_erase_of_mem hiT]; omega
  have hdiff : 0 < (A i \ (T.erase i).biUnion (fun j => A i ∩ A j)).card := by
    have := Finset.card_le_card_sdiff_add_card (s := A i) (t := (T.erase i).biUnion (fun j => A i ∩ A j))
    have h2 := hcard i
    omega
  obtain ⟨ℓ, hℓ⟩ := Finset.card_pos.mp hdiff
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_inter, not_exists,
    not_and] at hℓ
  have hv := congrFun h0 ℓ
  rw [lc_apply] at hv
  rw [Finset.sum_eq_single i] at hv
  · simp [hℓ.1] at hv
    exact hi hv
  · intro j _ hji
    by_cases hj : c j = 0
    · simp [hj]
    · have hjT : j ∈ T := by simp [hT, hj]
      have : ℓ ∉ A j := fun hlj => hℓ.2 j ⟨hji, hjT⟩ hℓ.1 hlj
      simp [this]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem wt_rep (hcard : ∀ i, (A i).card = e) (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g)
    (h7 : 7 * g < e) (c : ι → F) (hc : hammingNorm c ≤ 6) (E E' : ι) (α β : F)
    (h : lc A c = α • ind A E + β • ind A E') : hammingNorm c ≤ 2 := by
  set c' : ι → F := c - Pi.single E α - Pi.single E' β with hc'
  have hlc : lc A c' = 0 := by
    rw [hc', map_sub, map_sub, lc_single, lc_single, h]; simp
  have hw : hammingNorm c' ≤ 8 := by
    have : ∀ i, c' i ≠ 0 → i ∈ (Finset.univ.filter (fun i => c i ≠ 0)) ∪ {E, E'} := by
      intro i hi
      by_contra hn
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
        Finset.mem_insert, Finset.mem_singleton, not_not] at hn
      apply hi
      simp [hc', hn.1, hn.2.1, hn.2.2]
    refine (hammingNorm_le_of_subset c' _ this).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : ({E, E'} : Finset ι).card ≤ 2 := Finset.card_le_two
    have h2 : (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ 6 := hc
    omega
  have h0 := indep8 A e g hcard hinter h7 c' hw hlc
  have h3 : c - Pi.single E α - Pi.single E' β = 0 := h0
  have hcc : c = Pi.single E α + Pi.single E' β := by
    rw [sub_sub] at h3
    exact sub_eq_zero.mp h3
  have hsub : ∀ i, c i ≠ 0 → i ∈ ({E, E'} : Finset ι) := by
    intro i hi
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    apply hi
    rw [hcc]
    simp [Pi.single_apply, hn.1, hn.2]
  exact (hammingNorm_le_of_subset c _ hsub).trans Finset.card_le_two

end geo

section geo2
variable (A : ι → Finset L) (e g N : ℕ)

theorem sdiff_card_ge (hcard : ∀ i, (A i).card = e)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g) (hN : e = N + g) (i j : ι) (hij : i ≠ j) :
    N ≤ (A i \ A j).card := by
  have h1 := Finset.card_sdiff_add_card_inter (A i) (A j)
  have := hcard i
  have := hinter i j hij
  omega

theorem two_wt (hcard : ∀ i, (A i).card = e) (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g)
    (hN : e = N + g) (E E' : ι) (hEE : E ≠ E') (α β : F) (hα : α ≠ 0) (hβ : β ≠ 0) :
    2 * N ≤ hammingNorm (α • (ind A E : L → F) + β • ind A E') := by
  have h1 := sdiff_card_ge A e g N hcard hinter hN E E' hEE
  have h2 := sdiff_card_ge A e g N hcard hinter hN E' E hEE.symm
  have hdisj : Disjoint (A E \ A E') (A E' \ A E) := by
    rw [Finset.disjoint_left]
    intro ℓ h h'
    simp only [Finset.mem_sdiff] at h h'
    exact h'.2 h.1
  have hsub : (A E \ A E') ∪ (A E' \ A E) ⊆ Finset.univ.filter
      (fun ℓ => (α • (ind A E : L → F) + β • (ind A E' : L → F)) ℓ ≠ 0) := by
    intro ℓ hℓ
    simp only [Finset.mem_union, Finset.mem_sdiff] at hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.smul_apply, ind,
      smul_eq_mul]
    rcases hℓ with h | h
    · simp [h.1, h.2, hα]
    · simp [h.1, h.2, hβ]
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  rw [hammingNorm_eq]
  omega

theorem single_wt (hcard : ∀ i, (A i).card = e) (E : ι) (α : F) (hα : α ≠ 0) :
    hammingNorm (α • (ind A E : L → F)) = e := by
  rw [hammingNorm_eq, ← hcard E]
  congr 1
  ext ℓ
  by_cases h : ℓ ∈ A E <;> simp [ind, h, hα]

theorem union_card_ge (hcard : ∀ i, (A i).card = e)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g) (hN : e = N + g) (E E' : ι) (hEE : E ≠ E') :
    e + N ≤ (A E ∪ A E').card := by
  have := Finset.card_union_add_card_inter (A E) (A E')
  have := hcard E
  have := hcard E'
  have := hinter E E' hEE
  omega

theorem tri_card_ge (hcard : ∀ i, (A i).card = e)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g) (hN : e = N + g) (S : Finset L) (x y z : ι)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (h1 : A x \ A y ⊆ S) (h2 : A y \ A z ⊆ S) (h3 : A z \ A x ⊆ S) : 3 * N ≤ S.card := by
  have c1 := sdiff_card_ge A e g N hcard hinter hN x y hxy
  have c2 := sdiff_card_ge A e g N hcard hinter hN y z hyz
  have c3 := sdiff_card_ge A e g N hcard hinter hN z x hzx
  have d12 : Disjoint (A x \ A y) (A y \ A z) := by
    rw [Finset.disjoint_left]; intro ℓ h h'
    simp only [Finset.mem_sdiff] at h h'; exact h.2 h'.1
  have d23 : Disjoint (A y \ A z) (A z \ A x) := by
    rw [Finset.disjoint_left]; intro ℓ h h'
    simp only [Finset.mem_sdiff] at h h'; exact h.2 h'.1
  have d13 : Disjoint (A x \ A y ∪ A y \ A z) (A z \ A x) := by
    rw [Finset.disjoint_left]; intro ℓ h h'
    simp only [Finset.mem_union, Finset.mem_sdiff] at h h'
    rcases h with h | h
    · exact h'.2 h.1
    · exact h.2 h'.1
  have hsub : (A x \ A y ∪ A y \ A z) ∪ (A z \ A x) ⊆ S := Finset.union_subset
    (Finset.union_subset h1 h2) h3
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d13, Finset.card_union_of_disjoint d12] at this
  omega

end geo2

section item1
variable {p : ℕ} [Fact p.Prime]

theorem rep_vec (A : ι → Finset L) (E E' : ι) (α β : ZMod p) :
    ∃ c : ι → ZMod p, hammingNorm c ≤ 2 ∧
      lc A c = α • (ind A E : L → ZMod p) + β • (ind A E' : L → ZMod p) := by
  refine ⟨Pi.single E α + Pi.single E' β, ?_, ?_⟩
  · apply (hammingNorm_le_of_subset _ {E, E'} _).trans Finset.card_le_two
    intro i hi
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    apply hi
    simp [Pi.single_apply, hn.1, hn.2]
  · rw [map_add, lc_single, lc_single]

theorem span_supp (D : Set (ι → ZMod p)) (T : Finset ι) (hD : ∀ d ∈ D, ∀ k, k ∉ T → d k = 0)
    (x : ι → ZMod p) (hx : x ∈ Submodule.span (ZMod p) D) : ∀ k, k ∉ T → x k = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hD y hy
  | zero => intro k _; rfl
  | add y z _ _ hy hz => intro k hk; simp [hy k hk, hz k hk]
  | smul a y _ hy => intro k hk; simp [hy k hk]

theorem lc_mem (A : ι → Finset L) (V : Submodule (ZMod p) (L → ZMod p)) (D : Set (ι → ZMod p))
    (hD : ∀ d ∈ D, lc A d ∈ V) (x : ι → ZMod p) (hx : x ∈ Submodule.span (ZMod p) D) :
    lc A x ∈ V := by
  have : Submodule.span (ZMod p) D ≤ V.comap (lc A) := Submodule.span_le.mpr hD
  exact this hx

theorem lc_mem_span (A : ι → Finset L) (E E' : ι) (c : ι → ZMod p)
    (hc : ∀ k, k ≠ E → k ≠ E' → c k = 0) :
    lc A c ∈ Submodule.span (ZMod p) {(ind A E : L → ZMod p), ind A E'} := by
  have : lc A c = ∑ k, c k • (ind A k : L → ZMod p) := by
    simp [lc, Fintype.linearCombination_apply]
  rw [this]
  apply Submodule.sum_mem
  intro k _
  by_cases h1 : k = E
  · subst h1
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · by_cases h2 : k = E'
    · subst h2
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [hc k h1 h2, zero_smul]; exact Submodule.zero_mem _

theorem item1_abs [Nonempty ι] (A : ι → Finset L) (e g N : ℕ) (hcard : ∀ i, (A i).card = e)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g) (h7 : 7 * g < e) (hN : e = N + g)
    (V : Submodule (ZMod p) (L → ZMod p)) (S : Finset L)
    (hVS : ∀ v ∈ V, ∀ ℓ, ℓ ∉ S → v ℓ = 0)
    (hrep : ∀ v ∈ V, ∃ E E' : ι, ∃ α β : ZMod p,
      v = α • (ind A E : L → ZMod p) + β • (ind A E' : L → ZMod p))
    (hS : S.card < 3 * N) :
    ∃ E E' : ι, V ≤ Submodule.span (ZMod p) {(ind A E : L → ZMod p), ind A E'} := by
  classical
  obtain ⟨a0⟩ := ‹Nonempty ι›
  by_cases hV0 : ∀ v ∈ V, v = 0
  · refine ⟨a0, a0, ?_⟩
    intro v hv
    rw [hV0 v hv]; exact Submodule.zero_mem _
  push Not at hV0
  obtain ⟨v1, hv1, hv10⟩ := hV0
  obtain ⟨E, E', α, β, hv1e⟩ := hrep v1 hv1
  obtain ⟨c1, hc1w, hc1⟩ := rep_vec (p := p) A E E' α β
  rw [← hv1e] at hc1
  by_cases hsp : ∀ v ∈ V, v ∈ Submodule.span (ZMod p) {v1}
  · refine ⟨E, E', ?_⟩
    intro v hv
    have h1 : v1 ∈ Submodule.span (ZMod p) {(ind A E : L → ZMod p), ind A E'} := by
      rw [hv1e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h1)
    exact this (hsp v hv)
  push Not at hsp
  obtain ⟨v2, hv2, hv2n⟩ := hsp
  obtain ⟨F1, F2, γ, δ, hv2e⟩ := hrep v2 hv2
  obtain ⟨c2, hc2w, hc2⟩ := rep_vec (p := p) A F1 F2 γ δ
  rw [← hv2e] at hc2
  -- independence of c1, c2
  have hind : ∀ s t : ZMod p, s • c1 + t • c2 = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have h := congrArg (lc A) hst
    rw [map_add, map_smul, map_smul, hc1, hc2, map_zero] at h
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at h
      refine ⟨?_, rfl⟩
      by_contra hs
      exact hv10 (by simpa [hs] using h)
    · exfalso
      apply hv2n
      have : v2 = (-(t⁻¹ * s)) • v1 := by
        have h' : t • v2 = -(s • v1) := eq_neg_of_add_eq_zero_right h
        calc v2 = t⁻¹ • (t • v2) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • v1)) := by rw [h']
          _ = (-(t⁻¹ * s)) • v1 := by rw [smul_neg, smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hli : LinearIndependent (ZMod p) ![c1, c2] := LinearIndependent.pair_iff.mpr hind
  set M2 : Submodule (ZMod p) (ι → ZMod p) := Submodule.span (ZMod p) {c1, c2} with hM2
  have hfin2 : Module.finrank (ZMod p) M2 = 2 := by
    have := finrank_span_eq_card hli
    have hr : Set.range ![c1, c2] = {c1, c2} := by
      ext x; simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [hr] at this
    rw [hM2]
    simpa using this
  have hlcD : ∀ d ∈ ({c1, c2} : Set (ι → ZMod p)), lc A d ∈ V := by
    intro d hd
    rcases hd with rfl | hd
    · rw [hc1]; exact hv1
    · rw [Set.mem_singleton_iff.mp hd, hc2]; exact hv2
  -- every v ∈ V lies in the span of v1 v2
  have hall : ∀ v ∈ V, ∃ c ∈ M2, lc A c = v := by
    intro v hv
    obtain ⟨G1, G2, ε, ζ, hve⟩ := hrep v hv
    obtain ⟨c, hcw, hc⟩ := rep_vec (p := p) A G1 G2 ε ζ
    rw [← hve] at hc
    set M3 : Submodule (ZMod p) (ι → ZMod p) := Submodule.span (ZMod p) {c1, c2, c} with hM3
    have hM23 : M2 ≤ M3 := Submodule.span_mono (by intro x hx; simp at hx ⊢; tauto)
    obtain ⟨T, hTdef⟩ : ∃ T : Finset ι, T = (Finset.univ.filter (fun i => c1 i ≠ 0)) ∪
      (Finset.univ.filter (fun i => c2 i ≠ 0)) ∪ (Finset.univ.filter (fun i => c i ≠ 0)) :=
      ⟨_, rfl⟩
    have hT : T.card ≤ 6 := by
      rw [hTdef]
      have h1 := Finset.card_union_le ((Finset.univ.filter (fun i => c1 i ≠ 0)) ∪
        (Finset.univ.filter (fun i => c2 i ≠ 0))) (Finset.univ.filter (fun i => c i ≠ 0))
      have h2 := Finset.card_union_le (Finset.univ.filter (fun i => c1 i ≠ 0))
        (Finset.univ.filter (fun i => c2 i ≠ 0))
      have a1 : (Finset.univ.filter (fun i => c1 i ≠ 0)).card ≤ 2 := hc1w
      have a2 : (Finset.univ.filter (fun i => c2 i ≠ 0)).card ≤ 2 := hc2w
      have a3 : (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ 2 := hcw
      omega
    have hsupp3 := span_supp (p := p) {c1, c2, c} T (by
      intro d hd k hk
      by_contra hne
      have : k ∈ T := by
        rw [hTdef]
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hd with rfl | hd
        · exact Or.inl (Or.inl hne)
        · rcases hd with rfl | hd
          · exact Or.inl (Or.inr hne)
          · rw [Set.mem_singleton_iff] at hd; subst hd; exact Or.inr hne
      exact hk this)
    have hw3 : ∀ d ∈ M3, hammingNorm d ≤ 2 := by
      intro d hd
      have hdV : lc A d ∈ V := by
        apply lc_mem A V {c1, c2, c} _ d hd
        intro d' hd'
        rcases hd' with rfl | hd'
        · rw [hc1]; exact hv1
        · rcases hd' with rfl | hd'
          · rw [hc2]; exact hv2
          · rw [Set.mem_singleton_iff] at hd'; subst hd'; rw [hc]; exact hv
      obtain ⟨H1, H2, ε', ζ', hh⟩ := hrep _ hdV
      apply wt_rep A e g hcard hinter h7 d _ H1 H2 ε' ζ' hh
      exact (hammingNorm_le_of_subset d T (fun k hk => by
        by_contra hn; exact hk (hsupp3 d hd k hn))).trans hT
    have hcore := core p M3 hw3
    have hle : Module.finrank (ZMod p) M3 ≤ 2 := hcore.1
    have heq : M2 = M3 := Submodule.eq_of_le_of_finrank_le hM23 (by rw [hfin2]; exact hle)
    refine ⟨c, ?_, hc⟩
    rw [heq]
    exact Submodule.subset_span (by simp)
  have hsub : ∀ c ∈ M2, lc A c ∈ V := fun c hc => lc_mem A V _ hlcD c hc
  have hcoreM2 := core p M2 (by
    intro d hd
    have hdV := hsub d hd
    obtain ⟨H1, H2, ε', ζ', hh⟩ := hrep _ hdV
    apply wt_rep A e g hcard hinter h7 d _ H1 H2 ε' ζ' hh
    have hsupp2 := span_supp (p := p) {c1, c2}
      ((Finset.univ.filter (fun i => c1 i ≠ 0)) ∪ (Finset.univ.filter (fun i => c2 i ≠ 0)))
      (by
        intro d' hd' k hk
        by_contra hne
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rcases hd' with rfl | hd'
        · exact hk (Or.inl hne)
        · rw [Set.mem_singleton_iff] at hd'; subst hd'; exact hk (Or.inr hne))
      d hd
    refine (hammingNorm_le_of_subset d ((Finset.univ.filter (fun i => c1 i ≠ 0)) ∪
      (Finset.univ.filter (fun i => c2 i ≠ 0))) (fun k hk => by
      by_contra hn; exact hk (hsupp2 k hn))).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have a1 : (Finset.univ.filter (fun i => c1 i ≠ 0)).card ≤ 2 := hc1w
    have a2 : (Finset.univ.filter (fun i => c2 i ≠ 0)).card ≤ 2 := hc2w
    omega)
  rcases hcoreM2.2 with ⟨i, j, hij⟩ | ⟨-, x, y, z, hxy, hxz, hyz, hpxy, hpyz, hpzx⟩
  · refine ⟨i, j, ?_⟩
    intro v hv
    obtain ⟨c, hc, rfl⟩ := hall v hv
    exact lc_mem_span A i j c (fun k hki hkj => hij c hc k hki hkj)
  · exfalso
    have hxy' : (ind A x : L → ZMod p) + ind A y ∈ V := by
      have := hsub _ hpxy
      rwa [map_add, lc_single, lc_single, one_smul, one_smul] at this
    have hyz' : (ind A y : L → ZMod p) + ind A z ∈ V := by
      have := hsub _ hpyz
      rwa [map_add, lc_single, lc_single, one_smul, one_smul] at this
    have hzx' : (ind A z : L → ZMod p) + ind A x ∈ V := by
      have := hsub _ hpzx
      rwa [map_add, lc_single, lc_single, one_smul, one_smul] at this
    have key : ∀ a b : ι, (ind A a : L → ZMod p) + ind A b ∈ V → A a \ A b ⊆ S := by
      intro a b hab ℓ hℓ
      simp only [Finset.mem_sdiff] at hℓ
      by_contra hnS
      have := hVS _ hab ℓ hnS
      simp [ind, hℓ.1, hℓ.2] at this
    have := tri_card_ge A e g N hcard hinter hN S x y z hxy hyz hxz.symm (key x y hxy')
      (key y z hyz') (key z x hzx')
    omega

end item1

section item23
variable {p : ℕ} [Fact p.Prime]

theorem wt_le_card (v : L → ZMod p) (S : Finset L) (hVS : ∀ ℓ, ℓ ∉ S → v ℓ = 0) :
    hammingNorm v ≤ S.card :=
  hammingNorm_le_of_subset v S (fun ℓ hℓ => by by_contra h; exact hℓ (hVS ℓ h))

theorem wt_ge_e (A : ι → Finset L) (e g N : ℕ) (hcard : ∀ i, (A i).card = e)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g) (hN : e = N + g) (hgN : g ≤ N)
    (E E' : ι) (α β : ZMod p) (hv : α • (ind A E : L → ZMod p) + β • (ind A E' : L → ZMod p) ≠ 0) :
    e ≤ hammingNorm (α • (ind A E : L → ZMod p) + β • (ind A E' : L → ZMod p)) := by
  by_cases hα : α = 0
  · by_cases hβ : β = 0
    · exfalso; apply hv; simp [hα, hβ]
    · rw [hα, zero_smul, zero_add, single_wt A e hcard E' β hβ]
  · by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero, single_wt A e hcard E α hα]
    · by_cases hEE : E = E'
      · subst hEE
        have hs : α • (ind A E : L → ZMod p) + β • (ind A E : L → ZMod p) = (α + β) • ind A E := by
          rw [add_smul]
        rw [hs] at hv ⊢
        have : α + β ≠ 0 := by
          intro h; apply hv; rw [h, zero_smul]
        rw [single_wt A e hcard E _ this]
      · have := two_wt A e g N hcard hinter hN E E' hEE α β hα hβ
        omega

theorem item2_abs [Nonempty ι] (A : ι → Finset L) (e g N : ℕ) (hcard : ∀ i, (A i).card = e)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ g) (h7 : 7 * g < e) (hN : e = N + g)
    (V : Submodule (ZMod p) (L → ZMod p)) (S : Finset L)
    (hVS : ∀ v ∈ V, ∀ ℓ, ℓ ∉ S → v ℓ = 0)
    (hrep : ∀ v ∈ V, ∃ E E' : ι, ∃ α β : ZMod p,
      v = α • (ind A E : L → ZMod p) + β • (ind A E' : L → ZMod p))
    (hS2 : S.card < 2 * N) (hS3 : S.card < e + N) :
    ∃ E : ι, V ≤ Submodule.span (ZMod p) {(ind A E : L → ZMod p)} := by
  classical
  obtain ⟨E, E', hVE⟩ := item1_abs A e g N hcard hinter h7 hN V S hVS hrep (by omega)
  by_cases hEE : E = E'
  · subst hEE
    refine ⟨E, ?_⟩
    simpa using hVE
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hvn⟩ := Set.not_subset.mp (hcon E)
  obtain ⟨w, hw, hwn⟩ := Set.not_subset.mp (hcon E')
  obtain ⟨α, β, hvab⟩ := Submodule.mem_span_pair.mp (hVE hv)
  obtain ⟨γ, δ, hwab⟩ := Submodule.mem_span_pair.mp (hVE hw)
  -- v = α • indE + β • indE'  (mem_span_pair: α • x + β • y = v)
  have hβ : β ≠ 0 := by
    intro h; apply hvn; rw [← hvab, h, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hγ : γ ≠ 0 := by
    intro h; apply hwn; rw [← hwab, h, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hα : α = 0 := by
    by_contra hα
    have h1 := two_wt A e g N hcard hinter hN E E' hEE α β hα hβ
    have h2 := wt_le_card v S (hVS v hv)
    rw [hvab] at h1
    omega
  have hδ : δ = 0 := by
    by_contra hδ
    have h1 := two_wt A e g N hcard hinter hN E E' hEE γ δ hγ hδ
    have h2 := wt_le_card w S (hVS w hw)
    rw [hwab] at h1
    omega
  have hsub1 : A E' ⊆ S := by
    intro ℓ hℓ
    by_contra hnS
    have := hVS v hv ℓ hnS
    rw [← hvab, hα] at this
    simp [ind, hℓ, hβ] at this
  have hsub2 : A E ⊆ S := by
    intro ℓ hℓ
    by_contra hnS
    have := hVS w hw ℓ hnS
    rw [← hwab, hδ] at this
    simp [ind, hℓ, hγ] at this
  have := union_card_ge A e g N hcard hinter hN E E' hEE
  have := Finset.card_le_card (Finset.union_subset hsub2 hsub1)
  omega

end item23

section geoK
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

noncomputable def linesIn (U : Submodule K (Fin m → K)) : Finset (Lines K m) := by
  classical
  exact Finset.univ.filter (fun ℓ => ℓ.1 ≤ U)

theorem mem_linesIn (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesIn U ↔ ℓ.1 ≤ U := by
  classical
  simp [linesIn]

theorem card_linesIn (U : Submodule K (Fin m → K)) (d : ℕ) (hd : Module.finrank K U = d) :
    (linesIn U).card = (Fintype.card K ^ d - 1) / (Fintype.card K - 1) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesIn U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesIn]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hd, Nat.card_eq_fintype_card]
  rw [hc]

/-- the set of lines of a codimension-two subspace -/
noncomputable def sup2 (W : Codim2 K m) : Finset (Lines K m) := linesIn W.1

theorem card_sup2 (W : Codim2 K m) :
    (sup2 W).card = em (Fintype.card K) m := by
  unfold sup2 em
  apply card_linesIn
  have := W.2
  omega

theorem inter_sup2 [DecidableEq (Lines K m)] (W W' : Codim2 K m) (hne : W ≠ W') :
    (sup2 W ∩ sup2 W').card ≤ (Fintype.card K ^ (m - 3) - 1) / (Fintype.card K - 1) := by
  have h1 : sup2 W ∩ sup2 W' = linesIn (W.1 ⊓ W'.1) := by
    ext ℓ
    simp [sup2, mem_linesIn]
  rw [h1, card_linesIn _ (Module.finrank K ↥(W.1 ⊓ W'.1)) rfl]
  have hW := W.2
  have hW' := W'.2
  have hle : Module.finrank K ↥(W.1 ⊓ W'.1) ≤ m - 3 := by
    have h2 : Module.finrank K ↥(W.1 ⊓ W'.1) ≤ Module.finrank K W.1 :=
      Submodule.finrank_mono inf_le_left
    by_contra hcon
    have h3 : Module.finrank K ↥(W.1 ⊓ W'.1) = Module.finrank K W.1 := by omega
    have h4 : Module.finrank K ↥(W.1 ⊓ W'.1) = Module.finrank K W'.1 := by omega
    have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : W.1 ⊓ W'.1 ≤ W.1) h3
    have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : W.1 ⊓ W'.1 ≤ W'.1) h4
    exact hne (Subtype.ext (e1.symm.trans e2))
  have hQ : 0 < Fintype.card K := Fintype.card_pos
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right hQ hle

theorem exists_codim2 (hm : 2 ≤ m) : Nonempty (Codim2 K m) := by
  let f : (Fin m → K) →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi (fun j : Fin 2 => LinearMap.proj (Fin.castLE hm j))
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨fun i => if h : i.1 < 2 then y ⟨i.1, h⟩ else 0, ?_⟩
    funext j
    show (if h : (Fin.castLE hm j).1 < 2 then y ⟨(Fin.castLE hm j).1, h⟩ else 0) = y j
    rw [dif_pos (by simp only [Fin.val_castLE]; exact j.2)]
    rfl
  have h1 : Module.finrank K (LinearMap.range f) = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj]; simp
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  refine ⟨⟨LinearMap.ker f, ?_⟩⟩
  simp at h2
  omega

end geoK

end ProxGapTight.Dev.Shorten

namespace ProxGapTight
open ProxGapTight.Dev.Shorten

theorem chk_lemma_3_4_shortenings (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p ^ a →
      (∀ S : Finset (Lines K m), S.card ≤ Lm (p ^ a) m →
        ∃ W W' : Codim2 K m, shorten (Um K m p) S ≤
          Submodule.span (ZMod p) {incVec (ZMod p) W, incVec (ZMod p) W'}) ∧
      (∀ S : Finset (Lines K m), 3 * S.card ≤ 4 * em (p ^ a) m →
        ∃ W : Codim2 K m, shorten (Um K m p) S ≤ Submodule.span (ZMod p) {incVec (ZMod p) W}) ∧
      minDist (Um K m p) = em (p ^ a) m := by
  obtain ⟨m₀, hm₀⟩ := theorem_3_3_small_weight p a hQ h49 h121
  refine ⟨max m₀ 4, ?_⟩
  intro m hm K _ _ hK
  have hm0 : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  classical
  obtain ⟨g, M, hg, hM1, hN, he, hL, hMg, hg32⟩ := arith_facts (p ^ a) m (by omega) hm4
  have ht : 33 * M ≤ p ^ a * M := Nat.mul_le_mul_right _ (by omega)
  generalize p ^ a * M = t at *
  have hcard : ∀ W : Codim2 K m, (sup2 W).card = em (p ^ a) m := by
    intro W; rw [card_sup2, hK]
  have hinter : ∀ W W' : Codim2 K m, W ≠ W' → (sup2 W ∩ sup2 W').card ≤ g := by
    intro W W' hne
    have := inter_sup2 W W' hne
    rw [hK] at this
    rw [hg]; exact this
  have hN' : em (p ^ a) m = t + g := he
  have h7 : 7 * g < em (p ^ a) m := by omega
  have hinc : ∀ W : Codim2 K m, incVec (ZMod p) W = (ind sup2 W : Lines K m → ZMod p) := by
    intro W
    funext ℓ
    by_cases h : ℓ.1 ≤ W.1 <;> simp [incVec, ind, sup2, mem_linesIn, h]
  haveI hne : Nonempty (Codim2 K m) := exists_codim2 (by omega)
  have hrep : ∀ v ∈ Um K m p, hammingNorm v ≤ Lm (p ^ a) m →
      ∃ E E' : Codim2 K m, ∃ α β : ZMod p,
        v = α • (ind sup2 E : Lines K m → ZMod p) + β • (ind sup2 E' : Lines K m → ZMod p) := by
    intro v hv hw
    obtain ⟨W, W', α, β, h⟩ := hm₀ m hm0 K hK v hv hw
    exact ⟨W, W', α, β, by rw [h, hinc, hinc]⟩
  have hVS : ∀ (S : Finset (Lines K m)), ∀ v ∈ shorten (Um K m p) S, ∀ ℓ, ℓ ∉ S → v ℓ = 0 := by
    intro S v hv ℓ hℓ
    exact (Submodule.mem_inf.mp hv).2 ℓ hℓ
  have hrepV : ∀ (S : Finset (Lines K m)), S.card ≤ Lm (p ^ a) m →
      ∀ v ∈ shorten (Um K m p) S, ∃ E E' : Codim2 K m, ∃ α β : ZMod p,
        v = α • (ind sup2 E : Lines K m → ZMod p) + β • (ind sup2 E' : Lines K m → ZMod p) := by
    intro S hS v hv
    exact hrep v (Submodule.mem_inf.mp hv).1
      ((wt_le_card v S (hVS S v hv)).trans hS)
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨E, E', h⟩ := item1_abs (p := p) sup2 (em (p ^ a) m) g t hcard hinter h7 hN'
      (shorten (Um K m p) S) S (hVS S) (hrepV S hS) (by omega)
    exact ⟨E, E', by rw [hinc, hinc]; exact h⟩
  · intro S hS
    have hS' : S.card ≤ Lm (p ^ a) m := by omega
    obtain ⟨E, h⟩ := item2_abs (p := p) sup2 (em (p ^ a) m) g t hcard hinter h7 hN'
      (shorten (Um K m p) S) S (hVS S) (hrepV S hS') (by omega) (by omega)
    exact ⟨E, by rw [hinc]; exact h⟩
  · obtain ⟨W0⟩ := hne
    have hmem : incVec (ZMod p) W0 ∈ Um K m p := Submodule.subset_span (Set.mem_range_self W0)
    have hwt : hammingNorm (incVec (ZMod p) W0) = em (p ^ a) m := by
      have := single_wt (F := ZMod p) sup2 (em (p ^ a) m) hcard W0 1 one_ne_zero
      rw [one_smul] at this
      rw [hinc]; exact this
    have hne0 : incVec (ZMod p) W0 ≠ 0 := by
      intro h
      rw [h, hammingNorm_zero] at hwt
      omega
    have hmemS : em (p ^ a) m ∈ {w : ℕ | ∃ c ∈ Um K m p, c ≠ 0 ∧ hammingNorm c = w} :=
      ⟨_, hmem, hne0, hwt⟩
    unfold minDist
    apply le_antisymm
    · exact Nat.sInf_le hmemS
    · apply le_csInf ⟨_, hmemS⟩
      rintro w ⟨c, hc, hc0, rfl⟩
      by_cases hle : hammingNorm c ≤ Lm (p ^ a) m
      · obtain ⟨E, E', α, β, h⟩ := hrep c hc hle
        have := wt_ge_e (p := p) sup2 (em (p ^ a) m) g t hcard hinter hN' (by omega) E E' α β
          (by rw [← h]; exact hc0)
        rw [← h] at this
        exact this
      · omega

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_lemma_3_4_shortenings := @ProxGapTight.chk_lemma_3_4_shortenings
