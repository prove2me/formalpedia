-- Prove2me | solution 1 for ProbMetricStab.MixedInt.estimate_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:21:11.789807+00:00
-- url     : https://prove2.me/submissions/5fd920b5-c259-48a2-8e33-d428e537e7a2

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting
import Theorems.Thm_ProbMetricStab_MixedInt_lemma_3_5_b
import Theorems.Thm_ProbMetricStab_MixedInt_growth_bound

open MeasureTheory Matrix
open scoped ENNReal NNReal

section Helpers

open ProbMetricStab.MixedInt

/-! ### Section 1: Homogeneous Fourier-Motzkin elimination -/

private lemma fm_elim_one {r k : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (φ : F →+* ℝ) (hφ_strict : StrictMono φ) {I : Type} [Fintype I]
    (c : I → Fin r → F) (d : I → Fin (k + 1) → F) :
    ∃ (M : ℕ) (c' : Fin M → Fin r → F) (d' : Fin M → Fin k → F),
      (∀ l, (∀ i, c i l ≤ 0) → (∀ j, c' j l ≤ 0)) ∧
      ∀ (u : Fin r → ℝ) (y : Fin k → ℝ),
        (∃ z : ℝ, ∀ i, (∑ l, φ (c i l) * u l) +
            (∑ l : Fin k, φ (d i l.succ) * y l) + φ (d i 0) * z ≤ 0) ↔
        (∀ j, (∑ l, φ (c' j l) * u l) + (∑ l : Fin k, φ (d' j l) * y l) ≤ 0) := by
  classical
  let I₀ : Finset I := Finset.univ.filter (fun i => d i 0 = 0)
  let Ip : Finset I := Finset.univ.filter (fun i => 0 < d i 0)
  let Im : Finset I := Finset.univ.filter (fun i => d i 0 < 0)
  let J := {i : I // i ∈ I₀} ⊕ ({i : I // i ∈ Ip} × {i : I // i ∈ Im})
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let cJ : J → Fin r → F := fun j l =>
    match j with
    | Sum.inl i => c i.1 l
    | Sum.inr (ip, im) => (-d im.1 0) * c ip.1 l + d ip.1 0 * c im.1 l
  let dJ : J → Fin k → F := fun j l =>
    match j with
    | Sum.inl i => d i.1 l.succ
    | Sum.inr (ip, im) => (-d im.1 0) * d ip.1 l.succ + d ip.1 0 * d im.1 l.succ
  refine ⟨Fintype.card J, fun j => cJ (e.symm j), fun j => dJ (e.symm j), ?_, ?_⟩
  · intro l hcl j
    change cJ (e.symm j) l ≤ 0
    cases h : e.symm j with
    | inl i =>
      exact hcl i.1
    | inr p =>
      rcases p with ⟨⟨ip, hip⟩, ⟨im, him⟩⟩
      change (-d im 0) * c ip l + d ip 0 * c im l ≤ 0
      have hip' : 0 < d ip 0 := (Finset.mem_filter.mp hip).2
      have him' : d im 0 < 0 := (Finset.mem_filter.mp him).2
      have h1 : (-d im 0) * c ip l ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (hcl ip)
      have h2 : d ip 0 * c im l ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hip') (hcl im)
      linarith
  · intro u y
    let L : I → ℝ := fun i => (∑ l, φ (c i l) * u l) + ∑ l : Fin k, φ (d i l.succ) * y l
    have hJ_val : ∀ j : J, (∑ l, φ (cJ j l) * u l) + (∑ l : Fin k, φ (dJ j l) * y l) =
        match j with
        | Sum.inl i => L i.1
        | Sum.inr (ip, im) => φ (-d im.1 0) * L ip.1 + φ (d ip.1 0) * L im.1 := by
      intro j
      cases j with
      | inl i => rfl
      | inr p =>
        rcases p with ⟨ip, im⟩
        simp only [cJ, dJ, L, map_add, map_mul, add_mul, mul_assoc, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        ring
    constructor
    · rintro ⟨z, hz⟩ j
      dsimp only
      rw [hJ_val (e.symm j)]
      cases h : e.symm j with
      | inl i =>
        dsimp only
        have hi0 : d i.1 0 = 0 := (Finset.mem_filter.mp i.2).2
        have := hz i.1
        simp only [L, hi0, map_zero, zero_mul, add_zero] at this ⊢
        exact this
      | inr p =>
        rcases p with ⟨⟨ip, hip⟩, ⟨im, him⟩⟩
        dsimp only
        have hip' : (0 : ℝ) < φ (d ip 0) := by
          simpa using hφ_strict (Finset.mem_filter.mp hip).2
        have him' : φ (d im 0) < (0 : ℝ) := by
          simpa using hφ_strict (Finset.mem_filter.mp him).2
        have h1 : L ip + φ (d ip 0) * z ≤ 0 := hz ip
        have h2 : L im + φ (d im 0) * z ≤ 0 := hz im
        have hneg : φ (-d im 0) = -φ (d im 0) := map_neg φ _
        rw [hneg]
        nlinarith
    · intro hJ
      have h0 : ∀ i ∈ I₀, L i ≤ 0 := by
        intro i hi
        have hv : (∑ l, φ (cJ (Sum.inl ⟨i, hi⟩) l) * u l) +
            (∑ l : Fin k, φ (dJ (Sum.inl ⟨i, hi⟩) l) * y l) = L i := hJ_val (Sum.inl ⟨i, hi⟩)
        rw [← hv]
        have := hJ (e (Sum.inl ⟨i, hi⟩))
        simpa [e.symm_apply_apply] using this
      have hpm : ∀ ip ∈ Ip, ∀ im ∈ Im, -φ (d im 0) * L ip + φ (d ip 0) * L im ≤ 0 := by
        intro ip hip im him
        have hv : (∑ l, φ (cJ (Sum.inr (⟨ip, hip⟩, ⟨im, him⟩)) l) * u l) +
            (∑ l : Fin k, φ (dJ (Sum.inr (⟨ip, hip⟩, ⟨im, him⟩)) l) * y l) =
            φ (-d im 0) * L ip + φ (d ip 0) * L im := hJ_val (Sum.inr (⟨ip, hip⟩, ⟨im, him⟩))
        rw [map_neg] at hv
        rw [← hv]
        have := hJ (e (Sum.inr (⟨ip, hip⟩, ⟨im, him⟩)))
        simpa [e.symm_apply_apply] using this
      have htrich : ∀ i : I, i ∈ I₀ ∨ i ∈ Ip ∨ i ∈ Im := by
        intro i
        rcases lt_trichotomy (d i 0) 0 with h | h | h
        · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      by_cases hIm : Im.Nonempty
      · let z : ℝ := Im.sup' hIm (fun im => L im / (-φ (d im 0)))
        refine ⟨z, fun i => ?_⟩
        rcases htrich i with hi | hi | hi
        · have hi0 : d i 0 = 0 := (Finset.mem_filter.mp hi).2
          have := h0 i hi
          simp only [L, hi0, map_zero, zero_mul, add_zero] at this ⊢
          exact this
        · have hip' : (0 : ℝ) < φ (d i 0) := by
            simpa using hφ_strict (Finset.mem_filter.mp hi).2
          obtain ⟨im, him, hzm⟩ := Finset.exists_mem_eq_sup' hIm (fun im => L im / (-φ (d im 0)))
          have him' : (0 : ℝ) < -φ (d im 0) := by
            have : φ (d im 0) < 0 := by simpa using hφ_strict (Finset.mem_filter.mp him).2
            linarith
          have hpair := hpm i hi im him
          have hz_eq : z = L im / (-φ (d im 0)) := hzm
          change L i + φ (d i 0) * z ≤ 0
          rw [hz_eq]
          have hmul : (L i + φ (d i 0) * (L im / (-φ (d im 0)))) * (-φ (d im 0)) ≤ 0 := by
            have hdiv : L im / (-φ (d im 0)) * (-φ (d im 0)) = L im :=
              div_mul_cancel₀ _ (ne_of_gt him')
            calc (L i + φ (d i 0) * (L im / (-φ (d im 0)))) * (-φ (d im 0))
                = -φ (d im 0) * L i + φ (d i 0) * (L im / (-φ (d im 0)) * (-φ (d im 0))) := by ring
              _ = -φ (d im 0) * L i + φ (d i 0) * L im := by rw [hdiv]
              _ ≤ 0 := hpair
          exact nonpos_of_mul_nonpos_left hmul him'
        · have him' : (0 : ℝ) < -φ (d i 0) := by
            have : φ (d i 0) < 0 := by simpa using hφ_strict (Finset.mem_filter.mp hi).2
            linarith
          have hle : L i / (-φ (d i 0)) ≤ z := Finset.le_sup' (fun im => L im / (-φ (d im 0))) hi
          have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt him')
          rw [div_mul_cancel₀ _ (ne_of_gt him')] at hmul
          change L i + φ (d i 0) * z ≤ 0
          linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hIm
        by_cases hIp : Ip.Nonempty
        · let z : ℝ := Ip.inf' hIp (fun ip => (-L ip) / φ (d ip 0))
          refine ⟨z, fun i => ?_⟩
          rcases htrich i with hi | hi | hi
          · have hi0 : d i 0 = 0 := (Finset.mem_filter.mp hi).2
            have := h0 i hi
            simp only [L, hi0, map_zero, zero_mul, add_zero] at this ⊢
            exact this
          · have hip' : (0 : ℝ) < φ (d i 0) := by
              simpa using hφ_strict (Finset.mem_filter.mp hi).2
            have hle : z ≤ (-L i) / φ (d i 0) :=
              Finset.inf'_le (fun ip => (-L ip) / φ (d ip 0)) hi
            have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hip')
            rw [mul_div_cancel₀ _ (ne_of_gt hip')] at hmul
            change L i + φ (d i 0) * z ≤ 0
            linarith
          · rw [hIm] at hi
            exact absurd hi (Finset.notMem_empty _)
        · rw [Finset.not_nonempty_iff_eq_empty] at hIp
          refine ⟨0, fun i => ?_⟩
          rcases htrich i with hi | hi | hi
          · have hi0 : d i 0 = 0 := (Finset.mem_filter.mp hi).2
            have := h0 i hi
            simp only [L, hi0, map_zero, zero_mul, add_zero] at this ⊢
            exact this
          · rw [hIp] at hi; exact absurd hi (Finset.notMem_empty _)
          · rw [hIm] at hi; exact absurd hi (Finset.notMem_empty _)

private lemma fm_elim {r : ℕ} (k : ℕ) {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (φ : F →+* ℝ) (hφ_strict : StrictMono φ) {I : Type} [Fintype I]
    (c : I → Fin r → F) (d : I → Fin k → F) :
    ∃ (M : ℕ) (a : Fin M → Fin r → F),
      (∀ l, (∀ i, c i l ≤ 0) → (∀ j, a j l ≤ 0)) ∧
      ∀ u : Fin r → ℝ,
        (∃ y : Fin k → ℝ, ∀ i, (∑ l, φ (c i l) * u l) + (∑ l, φ (d i l) * y l) ≤ 0) ↔
        (∀ j, ∑ l, φ (a j l) * u l ≤ 0) := by
  induction k generalizing I with
  | zero =>
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    refine ⟨Fintype.card I, fun j => c (e.symm j), fun l hcl j => hcl (e.symm j), fun u => ?_⟩
    constructor
    · rintro ⟨_, hy⟩ j
      simpa using hy (e.symm j)
    · intro h
      refine ⟨Fin.elim0, fun i => ?_⟩
      simpa using h (e i)
  | succ k ih =>
    obtain ⟨M₁, c₁, d₁, hsign₁, hiff₁⟩ := fm_elim_one φ hφ_strict c d
    obtain ⟨M₂, a, hsign₂, hiff₂⟩ := ih c₁ d₁
    refine ⟨M₂, a, fun l hcl => hsign₂ l (hsign₁ l hcl), fun u => ?_⟩
    rw [← hiff₂ u]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨fun l => y l.succ, (hiff₁ u (fun l => y l.succ)).mp ⟨y 0, fun i => ?_⟩⟩
      have hi := hy i
      rw [Fin.sum_univ_succ] at hi
      linarith
    · rintro ⟨y', hy'⟩
      obtain ⟨z, hz⟩ := (hiff₁ u y').mpr hy'
      refine ⟨Fin.cons z y', fun i => ?_⟩
      have hi := hz i
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linarith

/-! ### Corollary 1A: Rational H-representation of `posWb` -/

private lemma posWb_int_halfspaces {r mh mb : ℕ} (R : Recourse r mh mb) (hB1 : R.B1) :
    ∃ (M : ℕ) (aZ : Fin M → Fin r → ℤ),
      ∀ u : EuclideanSpace ℝ (Fin r),
        u ∈ R.posWb ↔ ∀ j : Fin M, ∑ i : Fin r, (aZ j i : ℝ) * u i ≤ 0 := by
  classical
  choose WbQ hWbQ using hB1.2
  let I := Fin r ⊕ Fin r ⊕ Fin mb
  let c : I → Fin r → ℚ := fun idx l =>
    match idx with
    | Sum.inl i => if i = l then -1 else 0
    | Sum.inr (Sum.inl i) => if i = l then 1 else 0
    | Sum.inr (Sum.inr _) => 0
  let d : I → Fin mb → ℚ := fun idx j =>
    match idx with
    | Sum.inl i => WbQ i j
    | Sum.inr (Sum.inl i) => -WbQ i j
    | Sum.inr (Sum.inr k) => if k = j then -1 else 0
  obtain ⟨M, aQ, _, hiff⟩ := fm_elim mb (Rat.castHom ℝ) Rat.cast_strictMono c d
  let den : Fin M → ℕ := fun j => ∏ i : Fin r, (aQ j i).den
  have hden_pos : ∀ j, 0 < den j := fun j =>
    Finset.prod_pos fun i _ => (aQ j i).den_pos
  have hden_int : ∀ j i, ∃ z : ℤ, ((den j : ℚ) * aQ j i) = (z : ℚ) := by
    intro j i
    have hdvd : (aQ j i).den ∣ den j :=
      Finset.dvd_prod_of_mem (fun l => (aQ j l).den) (Finset.mem_univ i)
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨(q : ℤ) * (aQ j i).num, ?_⟩
    have hmul : ((aQ j i).den : ℚ) * aQ j i = ((aQ j i).num : ℚ) := by
      rw [mul_comm]; exact Rat.mul_den_eq_num (aQ j i)
    calc ((den j : ℚ) * aQ j i)
        = (q : ℚ) * (((aQ j i).den : ℚ) * aQ j i) := by
          rw [hq]; push_cast; ring
      _ = (q : ℚ) * ((aQ j i).num : ℚ) := by rw [hmul]
      _ = (((q : ℤ) * (aQ j i).num : ℤ) : ℚ) := by push_cast; ring
  choose aZ haZ using hden_int
  refine ⟨M, aZ, fun u => ?_⟩
  have hpos_iff : u ∈ R.posWb ↔
      ∃ yb : Fin mb → ℝ, ∀ idx : I,
        (∑ l, (c idx l : ℝ) * u l) + (∑ j, (d idx j : ℝ) * yb j) ≤ 0 := by
    constructor
    · rintro ⟨yb, hyb0, hybeq⟩
      refine ⟨yb, fun idx => ?_⟩
      cases idx with
      | inl i =>
        have hi : (R.Wb *ᵥ yb) i = u i := congr_arg (fun v : EuclideanSpace ℝ (Fin r) => v i) hybeq
        simp only [mulVec, dotProduct] at hi
        simp only [c, d, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
          ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        have hsum : ∑ j, (WbQ i j : ℝ) * yb j = u i := by
          simpa [← hWbQ] using hi
        linarith
      | inr idx' =>
        cases idx' with
        | inl i =>
          have hi : (R.Wb *ᵥ yb) i = u i := congr_arg (fun v : EuclideanSpace ℝ (Fin r) => v i) hybeq
          simp only [mulVec, dotProduct] at hi
          simp only [c, d, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
            ite_mul, one_mul, zero_mul, neg_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
            Finset.sum_neg_distrib]
          have hsum : ∑ j, (WbQ i j : ℝ) * yb j = u i := by
            simpa [← hWbQ] using hi
          linarith
        | inr k =>
          simp only [c, d, Rat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add,
            apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_neg, Rat.cast_one, ite_mul, neg_mul, one_mul,
            Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          have hk0 : (0 : ℝ) ≤ yb k := hyb0 k
          linarith
    · rintro ⟨yb, hyb⟩
      refine ⟨yb, fun k => ?_, ?_⟩
      · have hk := hyb (Sum.inr (Sum.inr k))
        simp only [c, d, Rat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add,
          apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_neg, Rat.cast_one, ite_mul, neg_mul, one_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hk
        change (0 : ℝ) ≤ yb k
        linarith
      · apply WithLp.ofLp_injective 2
        ext i
        have h1 := hyb (Sum.inl i)
        have h2 := hyb (Sum.inr (Sum.inl i))
        simp only [c, d, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
          ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
          Finset.sum_neg_distrib] at h1 h2
        change (R.Wb *ᵥ yb) i = u i
        simp only [mulVec, dotProduct]
        have hsum : ∑ j, R.Wb i j * yb j = ∑ j, (WbQ i j : ℝ) * yb j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hWbQ i j]
        rw [hsum]
        linarith
  simp only [Rat.coe_castHom] at hiff
  rw [hpos_iff, hiff u.ofLp]
  constructor
  · intro h j
    have hj := h j
    have hpos : (0 : ℝ) < (den j : ℝ) := by exact_mod_cast hden_pos j
    have hmul : (den j : ℝ) * ∑ i : Fin r, (aQ j i : ℝ) * u i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hj
    rw [Finset.mul_sum] at hmul
    have heq : ∀ i, (den j : ℝ) * ((aQ j i : ℝ) * u i) = (aZ j i : ℝ) * u i := by
      intro i
      have hcast : ((den j : ℝ) * (aQ j i : ℝ)) = (aZ j i : ℝ) := by
        have := congr_arg (Rat.cast : ℚ → ℝ) (haZ j i)
        simpa using this
      rw [← mul_assoc, hcast]
    simpa [heq] using hmul
  · intro h j
    have hj := h j
    have hpos : (0 : ℝ) < (den j : ℝ) := by exact_mod_cast hden_pos j
    have heq : ∀ i, (aZ j i : ℝ) * u i = (den j : ℝ) * ((aQ j i : ℝ) * u i) := by
      intro i
      have hcast : (aZ j i : ℝ) = ((den j : ℝ) * (aQ j i : ℝ)) := by
        have := congr_arg (Rat.cast : ℚ → ℝ) (haZ j i)
        simpa using this.symm
      rw [hcast, mul_assoc]
    simp_rw [heq, ← Finset.mul_sum] at hj
    exact nonpos_of_mul_nonpos_right hj hpos

/-! ### Corollary 1B: Dual representation and Lipschitzness of LP recourse `Φ_LP` -/

private lemma lp_recourse_lipschitz {r mh mb : ℕ} (R : Recourse r mh mb) (hB3 : R.B3) :
    ∃ (L_LP : ℝ) (φLP : EuclideanSpace ℝ (Fin r) → ℝ),
      0 < L_LP ∧
      (∀ u ∈ R.posWb, ∀ u' ∈ R.posWb, |φLP u - φLP u'| ≤ L_LP * ‖u - u'‖) ∧
      (∀ u ∈ R.posWb,
        (∃ yb : Fin mb → ℝ, 0 ≤ yb ∧ WithLp.toLp 2 (R.Wb *ᵥ yb) = u ∧ R.qb ⬝ᵥ yb ≤ φLP u) ∧
        (∀ yb : Fin mb → ℝ, 0 ≤ yb → WithLp.toLp 2 (R.Wb *ᵥ yb) = u → φLP u ≤ R.qb ⬝ᵥ yb)) := by
  classical
  let I := Fin r ⊕ Fin r ⊕ Fin mb ⊕ Unit
  let c : I → Fin (r + 1) → ℝ := fun idx l =>
    match idx with
    | Sum.inl i => if i.castSucc = l then -1 else 0
    | Sum.inr (Sum.inl i) => if i.castSucc = l then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr (Sum.inr (Sum.inr ())) => if l = Fin.last r then -1 else 0
  let d : I → Fin mb → ℝ := fun idx j =>
    match idx with
    | Sum.inl i => R.Wb i j
    | Sum.inr (Sum.inl i) => -R.Wb i j
    | Sum.inr (Sum.inr (Sum.inl k)) => if k = j then -1 else 0
    | Sum.inr (Sum.inr (Sum.inr ())) => R.qb j
  obtain ⟨M, a, hsign, hiff⟩ := fm_elim mb (RingHom.id ℝ) strictMono_id c d
  have ha_last : ∀ j : Fin M, a j (Fin.last r) ≤ 0 := by
    apply hsign (Fin.last r)
    intro idx
    cases idx with
    | inl i =>
      simp only [c, Fin.castSucc_ne_last, ↓reduceIte, le_refl]
    | inr idx' =>
      cases idx' with
      | inl i =>
        simp only [c, Fin.castSucc_ne_last, ↓reduceIte, le_refl]
      | inr idx'' =>
        cases idx'' with
        | inl _ => simp only [c, le_refl]
        | inr _ => simp only [c, ↓reduceIte]; norm_num
  have hepi : ∀ (u : EuclideanSpace ℝ (Fin r)) (α : ℝ),
      (∃ yb : Fin mb → ℝ, 0 ≤ yb ∧ WithLp.toLp 2 (R.Wb *ᵥ yb) = u ∧ R.qb ⬝ᵥ yb ≤ α) ↔
      (∀ j : Fin M, (∑ i : Fin r, a j i.castSucc * u i) + a j (Fin.last r) * α ≤ 0) := by
    intro u α
    let uα : Fin (r + 1) → ℝ := Fin.snoc u.ofLp α
    have hsys : (∃ yb : Fin mb → ℝ, 0 ≤ yb ∧ WithLp.toLp 2 (R.Wb *ᵥ yb) = u ∧ R.qb ⬝ᵥ yb ≤ α) ↔
        (∃ yb : Fin mb → ℝ, ∀ idx : I,
          (∑ l, c idx l * uα l) + (∑ j, d idx j * yb j) ≤ 0) := by
      constructor
      · rintro ⟨yb, hyb0, hybeq, hqle⟩
        refine ⟨yb, fun idx => ?_⟩
        cases idx with
        | inl i =>
          have hi : (R.Wb *ᵥ yb) i = u i := congr_arg (fun v : EuclideanSpace ℝ (Fin r) => v i) hybeq
          simp only [mulVec, dotProduct] at hi
          simp only [c, d, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ↓reduceIte, uα, Fin.snoc_castSucc]
          change -u i + ∑ j, R.Wb i j * yb j ≤ 0
          linarith
        | inr idx' =>
          cases idx' with
          | inl i =>
            have hi : (R.Wb *ᵥ yb) i = u i := congr_arg (fun v : EuclideanSpace ℝ (Fin r) => v i) hybeq
            simp only [mulVec, dotProduct] at hi
            simp only [c, d, ite_mul, one_mul, zero_mul, neg_mul, Finset.sum_ite_eq,
              Finset.mem_univ, ↓reduceIte, Finset.sum_neg_distrib, uα, Fin.snoc_castSucc]
            change u i + -(∑ j, R.Wb i j * yb j) ≤ 0
            linarith
          | inr idx'' =>
            cases idx'' with
            | inl k =>
              simp only [c, d, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, neg_mul,
                one_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
              have hk0 : (0 : ℝ) ≤ yb k := hyb0 k
              linarith
            | inr _ =>
              simp only [c, d, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq',
                Finset.mem_univ, ↓reduceIte, uα, Fin.snoc_last]
              change -α + R.qb ⬝ᵥ yb ≤ 0
              linarith
      · rintro ⟨yb, hyb⟩
        refine ⟨yb, fun k => ?_, ?_, ?_⟩
        · have hk := hyb (Sum.inr (Sum.inr (Sum.inl k)))
          simp only [c, d, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, neg_mul,
            one_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hk
          change (0 : ℝ) ≤ yb k
          linarith
        · apply WithLp.ofLp_injective 2
          ext i
          have h1 := hyb (Sum.inl i)
          have h2 := hyb (Sum.inr (Sum.inl i))
          simp only [c, d, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ↓reduceIte, Finset.sum_neg_distrib, uα, Fin.snoc_castSucc] at h1 h2
          change (R.Wb *ᵥ yb) i = u i
          simp only [mulVec, dotProduct]
          linarith
        · have hq := hyb (Sum.inr (Sum.inr (Sum.inr ())))
          simp only [c, d, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, uα, Fin.snoc_last] at hq
          change R.qb ⬝ᵥ yb ≤ α
          simp only [dotProduct]
          linarith
    simp only [RingHom.id_apply] at hiff
    rw [hsys, hiff uα]
    refine forall_congr' fun j => ?_
    rw [Fin.sum_univ_castSucc]
    simp only [uα, Fin.snoc_castSucc, Fin.snoc_last]
  let lam : Fin M → ℝ := fun j => -a j (Fin.last r)
  have hlam_nn : ∀ j, 0 ≤ lam j := fun j => neg_nonneg.mpr (ha_last j)
  let J : Finset (Fin M) := Finset.univ.filter (fun j => 0 < lam j)
  have hJne : J.Nonempty := by
    by_contra hJe
    rw [Finset.not_nonempty_iff_eq_empty] at hJe
    have h0 : ∀ j : Fin M, lam j = 0 := by
      intro j
      have hnot : j ∉ J := by rw [hJe]; exact Finset.notMem_empty _
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
      exact le_antisymm hnot (hlam_nn j)
    have hfeas : ∃ yb : Fin mb → ℝ, 0 ≤ yb ∧ WithLp.toLp 2 (R.Wb *ᵥ yb) = 0 ∧ R.qb ⬝ᵥ yb ≤ -1 := by
      rw [hepi 0 (-1)]
      intro j
      have haj : a j (Fin.last r) = 0 := by linarith [h0 j]
      simp [haj]
    obtain ⟨yb, hyb0, hybeq, hqle⟩ := hfeas
    obtain ⟨u₀, _, hWb_u⟩ := hB3
    have hzero : R.Wb *ᵥ yb = 0 := by
      have := congr_arg WithLp.ofLp hybeq
      exact this
    have hge : 0 ≤ R.qb ⬝ᵥ yb := by
      calc (0 : ℝ) = u₀ ⬝ᵥ (R.Wb *ᵥ yb) := by rw [hzero, dotProduct_zero]
        _ = (R.Wbᵀ *ᵥ u₀) ⬝ᵥ yb := by rw [dotProduct_mulVec, ← mulVec_transpose]
        _ ≤ R.qb ⬝ᵥ yb := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hWb_u j) (hyb0 j)
    linarith
  let v : Fin M → EuclideanSpace ℝ (Fin r) := fun j =>
    WithLp.toLp 2 (fun i => (lam j)⁻¹ * a j i.castSucc)
  let φLP : EuclideanSpace ℝ (Fin r) → ℝ := fun u =>
    J.sup' hJne (fun j => inner ℝ (v j) u)
  let L_LP : ℝ := J.sup' hJne (fun j => ‖v j‖) + 1
  have hL_pos : 0 < L_LP := by
    obtain ⟨j₀, hj₀⟩ := id hJne
    have : 0 ≤ J.sup' hJne (fun j => ‖v j‖) :=
      le_trans (norm_nonneg (v j₀)) (Finset.le_sup' (fun j => ‖v j‖) hj₀)
    linarith
  have hv_inner : ∀ j (u : EuclideanSpace ℝ (Fin r)),
      inner ℝ (v j) u = (lam j)⁻¹ * ∑ i : Fin r, a j i.castSucc * u i := by
    intro j u
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct, v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change u i * ((lam j)⁻¹ * a j i.castSucc) = (lam j)⁻¹ * (a j i.castSucc * u i)
    ring
  refine ⟨L_LP, φLP, hL_pos, ?_, ?_⟩
  · intro u _ u' _
    have hone : ∀ x y : EuclideanSpace ℝ (Fin r), φLP x - φLP y ≤ L_LP * ‖x - y‖ := by
      intro x y
      have hsup : φLP x ≤ φLP y + L_LP * ‖x - y‖ := by
        apply Finset.sup'_le
        intro j hj
        have hvle : ‖v j‖ ≤ L_LP := by
          have := Finset.le_sup' (f := fun j => ‖v j‖) hj
          dsimp only [L_LP]; linarith
        have hcs : inner ℝ (v j) (x - y) ≤ ‖v j‖ * ‖x - y‖ := real_inner_le_norm _ _
        have hlin : inner ℝ (v j) x = inner ℝ (v j) y + inner ℝ (v j) (x - y) := by
          rw [inner_sub_right]; ring
        have hyle : inner ℝ (v j) y ≤ φLP y := Finset.le_sup' (f := fun j => inner ℝ (v j) y) hj
        nlinarith [norm_nonneg (x - y)]
      linarith
    rw [abs_sub_le_iff]
    exact ⟨hone u u', by simpa [norm_sub_rev] using hone u' u⟩
  · intro u hu
    obtain ⟨yb₀, hyb₀0, hyb₀eq⟩ := hu
    have h0cond : ∀ j : Fin M, lam j = 0 → ∑ i : Fin r, a j i.castSucc * u i ≤ 0 := by
      intro j hj
      have hfeas := (hepi u (R.qb ⬝ᵥ yb₀)).mp ⟨yb₀, hyb₀0, hyb₀eq, le_refl _⟩ j
      have haj : a j (Fin.last r) = 0 := by linarith [hj]
      rw [haj, zero_mul, add_zero] at hfeas
      exact hfeas
    constructor
    · rw [hepi u (φLP u)]
      intro j
      by_cases hj : 0 < lam j
      · have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        have hle : inner ℝ (v j) u ≤ φLP u := Finset.le_sup' (f := fun j => inner ℝ (v j) u) hjJ
        rw [hv_inner] at hle
        have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hj)
        rw [mul_inv_cancel_left₀ (ne_of_gt hj)] at hmul
        have haj : a j (Fin.last r) = -lam j := by dsimp [lam]; ring
        rw [haj]
        linarith
      · have hj0 : lam j = 0 := le_antisymm (not_lt.mp hj) (hlam_nn j)
        have haj : a j (Fin.last r) = 0 := by linarith [hj0]
        rw [haj, zero_mul, add_zero]
        exact h0cond j hj0
    · intro yb hyb0 hybeq
      have hfeas := (hepi u (R.qb ⬝ᵥ yb)).mp ⟨yb, hyb0, hybeq, le_refl _⟩
      apply Finset.sup'_le
      intro j hjJ
      have hj : 0 < lam j := (Finset.mem_filter.mp hjJ).2
      have hfj := hfeas j
      have haj : a j (Fin.last r) = -lam j := by dsimp [lam]; ring
      rw [haj] at hfj
      rw [hv_inner]
      have hsum_le : ∑ i : Fin r, a j i.castSucc * u i ≤ lam j * (R.qb ⬝ᵥ yb) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (le_of_lt hj))
      rwa [inv_mul_cancel_left₀ (ne_of_gt hj)] at hmul

/-! ### Section 2: Lattice-cell Lipschitzness of `R.Phi` -/

private lemma phi_le_of_feasible {r mh mb : ℕ} (R : Recourse r mh mb)
    {t : EuclideanSpace ℝ (Fin r)} (y : Fin mh → ℕ) (yb : Fin mb → ℝ)
    (hyb : 0 ≤ yb) (heq : WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb) = t) :
    R.Phi t ≤ ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb : ℝ) : EReal) := by
  unfold Recourse.Phi
  exact iInf_le_of_le y (iInf_le_of_le yb (iInf_le_of_le hyb (iInf_le_of_le heq le_rfl)))

private lemma phi_lipschitz_on_cell {r mh mb : ℕ} (R : Recourse r mh mb)
    (hB1 : R.B1) (hB3 : R.B3) :
    ∃ (M : ℕ) (D : ℕ) (aZ : Fin M → Fin r → ℤ) (L_LP : ℝ),
      0 < D ∧ 0 < L_LP ∧
      ∀ t ∈ R.Tset, ∀ t' ∈ R.Tset,
        (∀ j : Fin M,
          ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉ =
          ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t' i⌉) →
        |(R.Phi t).toReal - (R.Phi t').toReal| ≤ L_LP * ‖t - t'‖ := by
  classical
  obtain ⟨M, aZ, hposWb⟩ := posWb_int_halfspaces R hB1
  obtain ⟨L_LP, φLP, hL_pos, hφ_lip, hφ_opt⟩ := lp_recourse_lipschitz R hB3
  have hfin := (ProbMetricStab.MixedInt.lemma_3_5_b R hB1 hB3).1
  choose WQ hWQ using hB1.1
  let D : ℕ := ∏ i : Fin r, ∏ l : Fin mh, (WQ i l).den
  have hD_pos : 0 < D := Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => (WQ i l).den_pos
  have hD_int : ∀ i l, ∃ z : ℤ, ((D : ℚ) * WQ i l) = (z : ℚ) := by
    intro i l
    have hdvd1 : (WQ i l).den ∣ ∏ l' : Fin mh, (WQ i l').den :=
      Finset.dvd_prod_of_mem (fun l' => (WQ i l').den) (Finset.mem_univ l)
    have hdvd2 : (∏ l' : Fin mh, (WQ i l').den) ∣ D :=
      Finset.dvd_prod_of_mem (fun i' => ∏ l' : Fin mh, (WQ i' l').den) (Finset.mem_univ i)
    obtain ⟨q, hq⟩ := dvd_trans hdvd1 hdvd2
    refine ⟨(q : ℤ) * (WQ i l).num, ?_⟩
    have hmul : ((WQ i l).den : ℚ) * WQ i l = ((WQ i l).num : ℚ) := by
      rw [mul_comm]; exact Rat.mul_den_eq_num (WQ i l)
    calc ((D : ℚ) * WQ i l)
        = (q : ℚ) * (((WQ i l).den : ℚ) * WQ i l) := by rw [hq]; push_cast; ring
      _ = (q : ℚ) * ((WQ i l).num : ℚ) := by rw [hmul]
      _ = (((q : ℤ) * (WQ i l).num : ℤ) : ℚ) := by push_cast; ring
  choose DWZ hDWZ using hD_int
  have hDWZ_real : ∀ i l, (D : ℝ) * R.W i l = (DWZ i l : ℝ) := by
    intro i l
    rw [hWQ i l]
    have := congr_arg (Rat.cast : ℚ → ℝ) (hDWZ i l)
    simpa using this
  have hWy_int : ∀ (j : Fin M) (y : Fin mh → ℕ),
      ∃ z : ℤ, (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) *
        (R.W *ᵥ (fun l => (y l : ℝ))) i = (z : ℝ) := by
    intro j y
    refine ⟨∑ i : Fin r, (aZ j i) * ∑ l : Fin mh, DWZ i l * (y l : ℤ), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hD := hDWZ_real i l
    calc (D : ℝ) * ((aZ j i : ℝ) * (R.W i l * (y l : ℝ)))
        = (aZ j i : ℝ) * (((D : ℝ) * R.W i l) * (y l : ℝ)) := by ring
      _ = (aZ j i : ℝ) * ((DWZ i l : ℝ) * (y l : ℝ)) := by rw [hD]
  have hsame_posWb : ∀ (t t' : EuclideanSpace ℝ (Fin r)),
      (∀ j : Fin M,
        ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉ =
        ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t' i⌉) →
      ∀ y : Fin mh → ℕ,
        t' - WithLp.toLp 2 (R.W *ᵥ (fun l => (y l : ℝ))) ∈ R.posWb →
        t - WithLp.toLp 2 (R.W *ᵥ (fun l => (y l : ℝ))) ∈ R.posWb := by
    intro t t' hcell y ht'
    rw [hposWb] at ht' ⊢
    intro j
    have hj' := ht' j
    have hD_posR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD_pos
    obtain ⟨z, hz⟩ := hWy_int j y
    have hsplit : ∀ v : EuclideanSpace ℝ (Fin r),
        (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) *
          (v - WithLp.toLp 2 (R.W *ᵥ (fun l => (y l : ℝ)))) i =
        (D : ℝ) * (∑ i : Fin r, (aZ j i : ℝ) * v i) - (z : ℝ) := by
      intro v
      rw [← hz]
      have : ∀ i : Fin r,
          (aZ j i : ℝ) * (v - WithLp.toLp 2 (R.W *ᵥ (fun l => (y l : ℝ)))) i =
          (aZ j i : ℝ) * v i - (aZ j i : ℝ) * (R.W *ᵥ (fun l => (y l : ℝ))) i := by
        intro i
        change (aZ j i : ℝ) * (v i - (R.W *ᵥ (fun l => (y l : ℝ))) i) = _
        ring
      simp_rw [this, Finset.sum_sub_distrib, mul_sub]
    have h1 : (D : ℝ) * (∑ i : Fin r, (aZ j i : ℝ) * t' i) ≤ (z : ℝ) := by
      have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD_posR) hj'
      rw [hsplit t'] at hm
      linarith
    have h2 : ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉ ≤ z := by
      rw [hcell j]
      exact Int.ceil_le.mpr h1
    have h3 : (D : ℝ) * (∑ i : Fin r, (aZ j i : ℝ) * t i) ≤ (z : ℝ) := Int.ceil_le.mp h2
    have h4 : (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) *
        (t - WithLp.toLp 2 (R.W *ᵥ (fun l => (y l : ℝ)))) i ≤ 0 := by
      rw [hsplit t]
      linarith
    exact nonpos_of_mul_nonpos_right h4 hD_posR
  have hone_side : ∀ t ∈ R.Tset, ∀ t' ∈ R.Tset,
      (∀ j : Fin M,
        ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉ =
        ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t' i⌉) →
      (R.Phi t).toReal - (R.Phi t').toReal ≤ L_LP * ‖t - t'‖ := by
    intro t ht t' ht' hcell
    have hER : R.Phi t ≤ R.Phi t' + ((L_LP * ‖t - t'‖ : ℝ) : EReal) := by
      have hge : ∀ (y : Fin mh → ℕ) (yb' : Fin mb → ℝ) (hyb' : 0 ≤ yb')
          (heq' : WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb') = t'),
          R.Phi t ≤ ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb' : ℝ) : EReal) +
            ((L_LP * ‖t - t'‖ : ℝ) : EReal) := by
        intro y yb' hyb' heq'
        let Wy : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)))
        have hWb_eq' : WithLp.toLp 2 (R.Wb *ᵥ yb') = t' - Wy := by
          apply WithLp.ofLp_injective 2
          have := congr_arg WithLp.ofLp heq'
          ext i
          have hi := congr_fun this i
          change (R.Wb *ᵥ yb') i = t' i - (R.W *ᵥ (fun i => (y i : ℝ))) i
          simp only [Pi.add_apply] at hi
          linarith
        have ht'_pos : t' - Wy ∈ R.posWb := ⟨yb', hyb', hWb_eq'⟩
        have ht_pos : t - Wy ∈ R.posWb := hsame_posWb t t' hcell y ht'_pos
        obtain ⟨yb, hyb0, hybeq, hq_le⟩ := (hφ_opt (t - Wy) ht_pos).1
        have hq_ge : φLP (t' - Wy) ≤ R.qb ⬝ᵥ yb' := (hφ_opt (t' - Wy) ht'_pos).2 yb' hyb' hWb_eq'
        have heq_t : WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb) = t := by
          apply WithLp.ofLp_injective 2
          have := congr_arg WithLp.ofLp hybeq
          ext i
          have hi := congr_fun this i
          change (R.W *ᵥ (fun i => (y i : ℝ))) i + (R.Wb *ᵥ yb) i = t i
          change (R.Wb *ᵥ yb) i = t i - (R.W *ᵥ (fun i => (y i : ℝ))) i at hi
          linarith
        have hphi_le := phi_le_of_feasible R y yb hyb0 heq_t
        have hlip := hφ_lip (t - Wy) ht_pos (t' - Wy) ht'_pos
        have hsub : (t - Wy) - (t' - Wy) = t - t' := sub_sub_sub_cancel_right t t' Wy
        rw [hsub] at hlip
        have hreal : R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb ≤
            R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb' + L_LP * ‖t - t'‖ := by
          have := (abs_sub_le_iff.mp hlip).1
          linarith
        calc R.Phi t
            ≤ ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb : ℝ) : EReal) := hphi_le
          _ ≤ ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb' + L_LP * ‖t - t'‖ : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.mpr hreal
          _ = ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb' : ℝ) : EReal) +
              ((L_LP * ‖t - t'‖ : ℝ) : EReal) := by rw [EReal.coe_add]
      have hfin_t := hfin t ht
      have hfin_t' := hfin t' ht'
      have hsub_le : R.Phi t - ((L_LP * ‖t - t'‖ : ℝ) : EReal) ≤ R.Phi t' := by
        conv_rhs => unfold Recourse.Phi
        refine le_iInf fun y => le_iInf fun yb' => le_iInf fun hyb' => le_iInf fun heq' => ?_
        have h1 := hge y yb' hyb' heq'
        rw [← EReal.coe_toReal hfin_t.1 hfin_t.2] at h1 ⊢
        rw [← EReal.coe_sub]
        rw [← EReal.coe_add] at h1
        exact EReal.coe_le_coe_iff.mpr (by linarith [EReal.coe_le_coe_iff.mp h1])
      rw [← EReal.coe_toReal hfin_t.1 hfin_t.2, ← EReal.coe_toReal hfin_t'.1 hfin_t'.2] at hsub_le ⊢
      rw [← EReal.coe_sub] at hsub_le
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith [EReal.coe_le_coe_iff.mp hsub_le])
    have hfin_t := hfin t ht
    have hfin_t' := hfin t' ht'
    rw [← EReal.coe_toReal hfin_t.1 hfin_t.2, ← EReal.coe_toReal hfin_t'.1 hfin_t'.2,
      ← EReal.coe_add] at hER
    linarith [EReal.coe_le_coe_iff.mp hER]
  refine ⟨M, D, aZ, L_LP, hD_pos, hL_pos, fun t ht t' ht' hcell => ?_⟩
  rw [abs_sub_le_iff]
  exact ⟨hone_side t ht t' ht' hcell,
    by simpa [norm_sub_rev] using hone_side t' ht' t ht (fun j => (hcell j).symm)⟩

/-! ### Section 3: Affine half-space pattern counting -/

private noncomputable def halfspacePat {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L : List ((E →ₗ[ℝ] ℝ) × ℝ)) (x : E) :
    Fin L.length → Bool :=
  fun i => decide ((L.get i).1 x ≤ (L.get i).2)

private lemma pow_succ_add_pow_le (N d : ℕ) :
    (N + 1) ^ (d + 1) + (N + 1) ^ d ≤ (N + 2) ^ (d + 1) := by
  induction d with
  | zero =>
    simp
  | succ d ih =>
    calc (N + 1) ^ (d + 2) + (N + 1) ^ (d + 1)
        = (N + 1) * ((N + 1) ^ (d + 1) + (N + 1) ^ d) := by ring
      _ ≤ (N + 1) * (N + 2) ^ (d + 1) := Nat.mul_le_mul_left _ ih
      _ ≤ (N + 2) * (N + 2) ^ (d + 1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = (N + 2) ^ (d + 2) := by ring

open Classical in
private lemma card_halfspacePat_le {r : ℕ} (L : List ((EuclideanSpace ℝ (Fin r) →ₗ[ℝ] ℝ) × ℝ)) :
    ∀ (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin r)) (V : Submodule ℝ (EuclideanSpace ℝ (Fin r))),
      Module.finrank ℝ V ≤ d →
      (Finset.univ.filter (fun p : Fin L.length → Bool =>
        ∃ x : EuclideanSpace ℝ (Fin r), x - x₀ ∈ V ∧ halfspacePat L x = p)).card ≤
      (L.length + 1) ^ d := by
  induction L with
  | nil =>
    intro d x₀ V _
    calc (Finset.univ.filter (fun p : Fin 0 → Bool =>
          ∃ x : EuclideanSpace ℝ (Fin r), x - x₀ ∈ V ∧ halfspacePat [] x = p)).card
        ≤ (Finset.univ : Finset (Fin 0 → Bool)).card := Finset.card_filter_le _ _
      _ = 1 := by simp
      _ = (0 + 1) ^ d := by simp
  | cons hd tl ih =>
    intro d x₀ V hdim
    rcases hd with ⟨ℓ, c⟩
    let N := tl.length
    let Pnew := Finset.univ.filter (fun q : Fin (N + 1) → Bool =>
      ∃ x : EuclideanSpace ℝ (Fin r), x - x₀ ∈ V ∧ halfspacePat ((ℓ, c) :: tl) x = q)
    let Pold := Finset.univ.filter (fun p : Fin N → Bool =>
      ∃ x : EuclideanSpace ℝ (Fin r), x - x₀ ∈ V ∧ halfspacePat tl x = p)
    let Psplit := Pold.filter (fun p =>
      (∃ x : EuclideanSpace ℝ (Fin r), x - x₀ ∈ V ∧ halfspacePat tl x = p ∧ ℓ x ≤ c) ∧
      (∃ x : EuclideanSpace ℝ (Fin r), x - x₀ ∈ V ∧ halfspacePat tl x = p ∧ ¬ ℓ x ≤ c))
    let tail : (Fin (N + 1) → Bool) → (Fin N → Bool) := fun q i => q i.succ
    have hpat_zero : ∀ x, halfspacePat ((ℓ, c) :: tl) x 0 = decide (ℓ x ≤ c) := fun _ => rfl
    have hpat_succ : ∀ x (i : Fin N),
        halfspacePat ((ℓ, c) :: tl) x i.succ = halfspacePat tl x i := fun _ _ => rfl
    have hcard_split : Pnew.card ≤ Pold.card + Psplit.card := by
      let f : (Fin (N + 1) → Bool) → (Fin N → Bool) ⊕ (Fin N → Bool) := fun q =>
        if q 0 = true then Sum.inl (tail q)
        else if tail q ∈ Psplit then Sum.inr (tail q)
        else Sum.inl (tail q)
      have hmaps : ∀ q ∈ Pnew, f q ∈ Pold.disjSum Psplit := by
        intro q hq
        obtain ⟨x, hxV, hxq⟩ := (Finset.mem_filter.mp hq).2
        have htail_mem : tail q ∈ Pold := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxV, ?_⟩
          ext i
          rw [← hpat_succ x i, hxq]
        dsimp only [f]
        split_ifs with h0 hs
        · exact Finset.mem_disjSum.mpr (Or.inl ⟨tail q, htail_mem, rfl⟩)
        · exact Finset.mem_disjSum.mpr (Or.inr ⟨tail q, hs, rfl⟩)
        · exact Finset.mem_disjSum.mpr (Or.inl ⟨tail q, htail_mem, rfl⟩)
      have hinj : Set.InjOn f (Pnew : Set (Fin (N + 1) → Bool)) := by
        intro q₁ hq₁ q₂ hq₂ hfeq
        have hq₁' : q₁ ∈ Pnew := hq₁
        have hq₂' : q₂ ∈ Pnew := hq₂
        obtain ⟨x₁, hx₁V, hx₁q⟩ := (Finset.mem_filter.mp hq₁').2
        obtain ⟨x₂, hx₂V, hx₂q⟩ := (Finset.mem_filter.mp hq₂').2
        have hsame_tail : tail q₁ = tail q₂ := by
          dsimp only [f] at hfeq
          split_ifs at hfeq <;> simp_all
        have hsame_zero : q₁ 0 = q₂ 0 := by
          by_contra hne
          have hmem_split : tail q₁ ∈ Psplit := by
            have htail_mem : tail q₁ ∈ Pold := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x₁, hx₁V, ?_⟩
              ext i; rw [← hpat_succ x₁ i, hx₁q]
            refine Finset.mem_filter.mpr ⟨htail_mem, ?_, ?_⟩
            · cases hq10 : q₁ 0
              · have hq20 : q₂ 0 = true := by
                  cases h2 : q₂ 0
                  · exact absurd (hq10.trans h2.symm) hne
                  · rfl
                refine ⟨x₂, hx₂V, ?_, ?_⟩
                · ext i; rw [← hpat_succ x₂ i, hx₂q]; exact (congr_fun hsame_tail i).symm
                · have : decide (ℓ x₂ ≤ c) = true := by rw [← hpat_zero x₂, hx₂q, hq20]
                  exact of_decide_eq_true this
              · refine ⟨x₁, hx₁V, ?_, ?_⟩
                · ext i; rw [← hpat_succ x₁ i, hx₁q]
                · have : decide (ℓ x₁ ≤ c) = true := by rw [← hpat_zero x₁, hx₁q, hq10]
                  exact of_decide_eq_true this
            · cases hq10 : q₁ 0
              · refine ⟨x₁, hx₁V, ?_, ?_⟩
                · ext i; rw [← hpat_succ x₁ i, hx₁q]
                · have : decide (ℓ x₁ ≤ c) = false := by rw [← hpat_zero x₁, hx₁q, hq10]
                  exact of_decide_eq_false this
              · have hq20 : q₂ 0 = false := by
                  cases h2 : q₂ 0
                  · rfl
                  · exact absurd (hq10.trans h2.symm) hne
                refine ⟨x₂, hx₂V, ?_, ?_⟩
                · ext i; rw [← hpat_succ x₂ i, hx₂q]; exact (congr_fun hsame_tail i).symm
                · have : decide (ℓ x₂ ≤ c) = false := by rw [← hpat_zero x₂, hx₂q, hq20]
                  exact of_decide_eq_false this
          have hmem_split2 : tail q₂ ∈ Psplit := hsame_tail ▸ hmem_split
          dsimp only [f] at hfeq
          cases h1 : q₁ 0 <;> cases h2 : q₂ 0 <;> simp [h1, h2, hmem_split, hmem_split2] at hfeq hne
        ext i
        refine Fin.cases hsame_zero (fun j => congr_fun hsame_tail j) i
      calc Pnew.card
          ≤ (Pold.disjSum Psplit).card := Finset.card_le_card_of_injOn f hmaps hinj
        _ = Pold.card + Psplit.card := Finset.card_disjSum _ _
    have hold_le : Pold.card ≤ (N + 1) ^ d := ih d x₀ V hdim
    cases d with
    | zero =>
      have hVbot : V = ⊥ := by
        have h0 : Module.finrank ℝ V = 0 := Nat.eq_zero_of_le_zero hdim
        exact Submodule.finrank_eq_zero.mp h0
      have hsplit_empty : Psplit = ∅ := by
        ext p
        simp only [Finset.notMem_empty, iff_false]
        intro hp
        obtain ⟨_, ⟨x₁, hx₁V, _, hle₁⟩, ⟨x₂, hx₂V, _, hgt₂⟩⟩ := Finset.mem_filter.mp hp
        rw [hVbot, Submodule.mem_bot, sub_eq_zero] at hx₁V hx₂V
        rw [hx₁V] at hle₁
        rw [hx₂V] at hgt₂
        exact hgt₂ hle₁
      rw [hsplit_empty, Finset.card_empty, add_zero] at hcard_split
      simpa using le_trans hcard_split hold_le
    | succ d' =>
      by_cases hsp : Psplit.Nonempty
      · obtain ⟨p₀, hp₀⟩ := hsp
        obtain ⟨_, ⟨y₁, hy₁V, _, hle₁⟩, ⟨y₂, hy₂V, _, hgt₂⟩⟩ := Finset.mem_filter.mp hp₀
        have hlt : ℓ y₁ < ℓ y₂ := lt_of_le_of_lt hle₁ (not_le.mp hgt₂)
        let t₀ : ℝ := (c - ℓ y₁) / (ℓ y₂ - ℓ y₁)
        let xStar : EuclideanSpace ℝ (Fin r) := (1 - t₀) • y₁ + t₀ • y₂
        have hxStarV : xStar - x₀ ∈ V := by
          have hsub : xStar - x₀ = (1 - t₀) • (y₁ - x₀) + t₀ • (y₂ - x₀) := by
            dsimp only [xStar]; module
          rw [hsub]
          exact V.add_mem (V.smul_mem _ hy₁V) (V.smul_mem _ hy₂V)
        have hℓStar : ℓ xStar = c := by
          dsimp only [xStar, t₀]
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hne : ℓ y₂ - ℓ y₁ ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
          field_simp [hne]
          ring
        let V' : Submodule ℝ (EuclideanSpace ℝ (Fin r)) := V ⊓ LinearMap.ker ℓ
        have hV'_lt : V' < V := by
          refine lt_of_le_of_ne inf_le_left ?_
          intro heq
          have hmemV : y₂ - y₁ ∈ V := by
            have : y₂ - y₁ = (y₂ - x₀) - (y₁ - x₀) := by abel
            rw [this]
            exact V.sub_mem hy₂V hy₁V
          rw [← heq] at hmemV
          have hker : ℓ (y₂ - y₁) = 0 := hmemV.2
          rw [map_sub] at hker
          linarith
        have hdim' : Module.finrank ℝ V' ≤ d' := by
          have hlt_rank : Module.finrank ℝ V' < Module.finrank ℝ V :=
            Submodule.finrank_lt_finrank_of_lt hV'_lt
          omega
        have hsub_split : Psplit ⊆ Finset.univ.filter (fun p : Fin N → Bool =>
            ∃ x : EuclideanSpace ℝ (Fin r), x - xStar ∈ V' ∧ halfspacePat tl x = p) := by
          intro p hp
          obtain ⟨_, ⟨x₁, hx₁V, hx₁p, hx₁le⟩, ⟨x₂, hx₂V, hx₂p, hx₂gt⟩⟩ := Finset.mem_filter.mp hp
          have hxlt : ℓ x₁ < ℓ x₂ := lt_of_le_of_lt hx₁le (not_le.mp hx₂gt)
          let t : ℝ := (c - ℓ x₁) / (ℓ x₂ - ℓ x₁)
          have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx₁le) (sub_nonneg.mpr (le_of_lt hxlt))
          have ht1 : t < 1 := by
            rw [div_lt_one (sub_pos.mpr hxlt)]
            linarith [not_le.mp hx₂gt]
          have h1t : 0 < 1 - t := sub_pos.mpr ht1
          let x : EuclideanSpace ℝ (Fin r) := (1 - t) • x₁ + t • x₂
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, ?_, ?_⟩
          · constructor
            · have hxV : x - x₀ ∈ V := by
                have : x - x₀ = (1 - t) • (x₁ - x₀) + t • (x₂ - x₀) := by dsimp only [x]; module
                rw [this]
                exact V.add_mem (V.smul_mem _ hx₁V) (V.smul_mem _ hx₂V)
              have : x - xStar = (x - x₀) - (xStar - x₀) := by abel
              rw [this]
              exact V.sub_mem hxV hxStarV
            · change ℓ (x - xStar) = 0
              rw [map_sub, hℓStar]
              have hℓx : ℓ x = c := by
                dsimp only [x, t]
                rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
                have hne : ℓ x₂ - ℓ x₁ ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
                field_simp [hne]
                ring
              linarith
          · ext i
            have hi1 : decide ((tl.get i).1 x₁ ≤ (tl.get i).2) = p i := congr_fun hx₁p i
            have hi2 : decide ((tl.get i).1 x₂ ≤ (tl.get i).2) = p i := congr_fun hx₂p i
            change decide ((tl.get i).1 x ≤ (tl.get i).2) = p i
            have hlin : (tl.get i).1 x = (1 - t) * (tl.get i).1 x₁ + t * (tl.get i).1 x₂ := by
              dsimp only [x]
              rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
            cases hpi : p i
            · rw [hpi] at hi1 hi2
              have hgt1 : (tl.get i).2 < (tl.get i).1 x₁ := not_le.mp (of_decide_eq_false hi1)
              have hgt2 : (tl.get i).2 < (tl.get i).1 x₂ := not_le.mp (of_decide_eq_false hi2)
              have hgt : (tl.get i).2 < (tl.get i).1 x := by
                rw [hlin]
                nlinarith
              exact decide_eq_false (not_le.mpr hgt)
            · rw [hpi] at hi1 hi2
              have hle1 : (tl.get i).1 x₁ ≤ (tl.get i).2 := of_decide_eq_true hi1
              have hle2 : (tl.get i).1 x₂ ≤ (tl.get i).2 := of_decide_eq_true hi2
              have hle : (tl.get i).1 x ≤ (tl.get i).2 := by
                rw [hlin]
                nlinarith
              exact decide_eq_true hle
        have hsplit_le : Psplit.card ≤ (N + 1) ^ d' :=
          le_trans (Finset.card_le_card hsub_split) (ih d' xStar V' hdim')
        calc Pnew.card
            ≤ Pold.card + Psplit.card := hcard_split
          _ ≤ (N + 1) ^ (d' + 1) + (N + 1) ^ d' := Nat.add_le_add hold_le hsplit_le
          _ ≤ (N + 2) ^ (d' + 1) := pow_succ_add_pow_le N d'
      · rw [Finset.not_nonempty_iff_eq_empty] at hsp
        rw [hsp, Finset.card_empty, add_zero] at hcard_split
        calc Pnew.card ≤ Pold.card := hcard_split
          _ ≤ (N + 1) ^ (d' + 1) := hold_le
          _ ≤ (N + 2) ^ (d' + 1) := Nat.pow_le_pow_left (Nat.le_succ _) _

private lemma cell_count_ball {r M : ℕ} (D : ℕ) (hD : 0 < D) (aZ : Fin M → Fin r → ℤ) :
    ∃ C_H : ℝ, 0 < C_H ∧
      ∀ R : ℝ, 1 ≤ R →
        ∃ S : Finset (Fin M → ℤ),
          (∀ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R,
            (fun j => ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉) ∈ S) ∧
          (S.card : ℝ) ≤ (C_H * R) ^ r := by
  classical
  let aVec : Fin M → EuclideanSpace ℝ (Fin r) := fun j => WithLp.toLp 2 (fun i => (aZ j i : ℝ))
  let C_H : ℝ := 1 + ∑ j : Fin M, (2 * (D : ℝ) * ‖aVec j‖ + 5)
  have hCH_pos : 0 < C_H := by
    have : 0 ≤ ∑ j : Fin M, (2 * (D : ℝ) * ‖aVec j‖ + 5) :=
      Finset.sum_nonneg fun j _ => by positivity
    linarith
  refine ⟨C_H, hCH_pos, fun R hR => ?_⟩
  let B : Fin M → ℕ := fun j => Nat.ceil ((D : ℝ) * ‖aVec j‖ * R) + 1
  let box : Finset (Fin M → ℤ) :=
    Fintype.piFinset fun j => Finset.Icc (-(B j : ℤ)) (B j : ℤ)
  let cellIdx : EuclideanSpace ℝ (Fin r) → (Fin M → ℤ) := fun t j =>
    ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉
  have hmem_box : ∀ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R,
      cellIdx t ∈ box := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    have hinner : ∑ i : Fin r, (aZ j i : ℝ) * t i = inner ℝ (aVec j) t := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, aVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (aZ j i : ℝ) * t i = t i * (aZ j i : ℝ)
      ring
    have habs : |(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i| ≤ (D : ℝ) * ‖aVec j‖ * R := by
      rw [hinner, abs_mul, Nat.abs_cast]
      have hcs : |inner ℝ (aVec j) t| ≤ ‖aVec j‖ * ‖t‖ := abs_real_inner_le_norm _ _
      have h1 : |inner ℝ (aVec j) t| ≤ ‖aVec j‖ * R :=
        le_trans hcs (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
      calc (D : ℝ) * |inner ℝ (aVec j) t|
          ≤ (D : ℝ) * (‖aVec j‖ * R) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = (D : ℝ) * ‖aVec j‖ * R := (mul_assoc _ _ _).symm
    have hBle : (D : ℝ) * ‖aVec j‖ * R ≤ (B j : ℝ) := by
      dsimp only [B]
      push_cast
      linarith [Nat.le_ceil ((D : ℝ) * ‖aVec j‖ * R)]
    have hle := (abs_le.mp (le_trans habs hBle))
    refine ⟨?_, ?_⟩
    · have : (-(B j : ℤ) : ℝ) ≤ (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i := by
        simpa using hle.1
      have hlt : (-(B j : ℤ) : ℝ) ≤ (cellIdx t j : ℝ) := le_trans this (Int.le_ceil _)
      exact_mod_cast hlt
    · exact Int.ceil_le.mpr (by simpa using hle.2)
  let S : Finset (Fin M → ℤ) := box.filter (fun κ =>
    ∃ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R, cellIdx t = κ)
  refine ⟨S, fun t ht => Finset.mem_filter.mpr ⟨hmem_box t ht, t, ht, rfl⟩, ?_⟩
  let ℓj : Fin M → (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] ℝ) := fun j =>
    { toFun := fun t => (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i
      map_add' := fun x y => by
        simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c x => by
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        calc (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * (c * x i)
            = (D : ℝ) * ∑ i : Fin r, c * ((aZ j i : ℝ) * x i) := by
              congr 1; exact Finset.sum_congr rfl fun i _ => by ring
          _ = c * ((D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * x i) := by
              rw [← Finset.mul_sum]; ring }
  let L : List ((EuclideanSpace ℝ (Fin r) →ₗ[ℝ] ℝ) × ℝ) :=
    (List.finRange M).flatMap fun j =>
      ((Finset.Icc (-(B j : ℤ)) (B j : ℤ)).toList).map fun (k : ℤ) => (ℓj j, (k : ℝ))
  let P := Finset.univ.filter (fun p : Fin L.length → Bool =>
    ∃ t : EuclideanSpace ℝ (Fin r), t - 0 ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin r))) ∧
      halfspacePat L t = p)
  have hS_le_P : S.card ≤ P.card := by
    have hchoose : ∀ κ ∈ S, ∃ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R,
        cellIdx t = κ := fun κ hκ => (Finset.mem_filter.mp hκ).2
    let rep : (Fin M → ℤ) → EuclideanSpace ℝ (Fin r) := fun κ =>
      if h : κ ∈ S then (hchoose κ h).choose else 0
    have hrep_spec : ∀ κ (h : κ ∈ S),
        rep κ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R ∧ cellIdx (rep κ) = κ := by
      intro κ h
      simpa [rep, h] using (hchoose κ h).choose_spec
    let g : (Fin M → ℤ) → (Fin L.length → Bool) := fun κ => halfspacePat L (rep κ)
    have hmaps : ∀ κ ∈ S, g κ ∈ P := by
      intro κ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rep κ, Submodule.mem_top, rfl⟩
    have hinj : Set.InjOn g (S : Set (Fin M → ℤ)) := by
      intro κ₁ hκ₁ κ₂ hκ₂ hgeq
      have h1 := hrep_spec κ₁ hκ₁
      have h2 := hrep_spec κ₂ hκ₂
      have hbox1 : κ₁ ∈ box := (Finset.mem_filter.mp hκ₁).1
      have hbox2 : κ₂ ∈ box := (Finset.mem_filter.mp hκ₂).1
      have hpair : ∀ (j : Fin M) (k : ℤ), k ∈ Finset.Icc (-(B j : ℤ)) (B j : ℤ) →
          (ℓj j (rep κ₁) ≤ (k : ℝ) ↔ ℓj j (rep κ₂) ≤ (k : ℝ)) := by
        intro j k hk
        have hmemL : (ℓj j, (k : ℝ)) ∈ L :=
          List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
            List.mem_map.mpr ⟨k, Finset.mem_toList.mpr hk, rfl⟩⟩
        obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hmemL
        have heq_idx : halfspacePat L (rep κ₁) idx = halfspacePat L (rep κ₂) idx :=
          congr_fun hgeq idx
        simp only [halfspacePat, hidx] at heq_idx
        exact decide_eq_decide.mp heq_idx
      ext j
      have hk1 : κ₁ j ∈ Finset.Icc (-(B j : ℤ)) (B j : ℤ) := Fintype.mem_piFinset.mp hbox1 j
      have hk2 : κ₂ j ∈ Finset.Icc (-(B j : ℤ)) (B j : ℤ) := Fintype.mem_piFinset.mp hbox2 j
      have h12 : κ₁ j ≤ κ₂ j := by
        have hle2 : ℓj j (rep κ₂) ≤ (κ₂ j : ℝ) := by
          have := Int.le_ceil (ℓj j (rep κ₂))
          have hc := congr_fun h2.2 j
          change ⌈ℓj j (rep κ₂)⌉ = κ₂ j at hc
          rwa [hc] at this
        have hle1 : ℓj j (rep κ₁) ≤ (κ₂ j : ℝ) := (hpair j (κ₂ j) hk2).mpr hle2
        have hc := congr_fun h1.2 j
        change ⌈ℓj j (rep κ₁)⌉ = κ₁ j at hc
        rw [← hc]
        exact Int.ceil_le.mpr hle1
      have h21 : κ₂ j ≤ κ₁ j := by
        have hle1 : ℓj j (rep κ₁) ≤ (κ₁ j : ℝ) := by
          have := Int.le_ceil (ℓj j (rep κ₁))
          have hc := congr_fun h1.2 j
          change ⌈ℓj j (rep κ₁)⌉ = κ₁ j at hc
          rwa [hc] at this
        have hle2 : ℓj j (rep κ₂) ≤ (κ₁ j : ℝ) := (hpair j (κ₁ j) hk1).mp hle1
        have hc := congr_fun h2.2 j
        change ⌈ℓj j (rep κ₂)⌉ = κ₂ j at hc
        rw [← hc]
        exact Int.ceil_le.mpr hle2
      exact le_antisymm h12 h21
    exact Finset.card_le_card_of_injOn g hmaps hinj
  have hP_le : P.card ≤ (L.length + 1) ^ r := by
    apply card_halfspacePat_le L r 0 ⊤
    simp [finrank_top]
  have hL_len : (L.length : ℝ) + 1 ≤ C_H * R := by
    have hlen_eq : L.length = ∑ j : Fin M, (2 * B j + 1) := by
      dsimp only [L]
      rw [List.length_flatMap]
      have hmap : ∀ j : Fin M,
          (((Finset.Icc (-(B j : ℤ)) (B j : ℤ)).toList).map fun (k : ℤ) => (ℓj j, (k : ℝ))).length =
          2 * B j + 1 := by
        intro j
        rw [List.length_map, Finset.length_toList, Int.card_Icc]
        omega
      simp_rw [hmap]
      rw [← Fin.sum_univ_def]
    rw [hlen_eq]
    push_cast
    have hterm : ∀ j : Fin M, (2 * (B j : ℝ) + 1) ≤ (2 * (D : ℝ) * ‖aVec j‖ + 5) * R := by
      intro j
      have hceil : (Nat.ceil ((D : ℝ) * ‖aVec j‖ * R) : ℝ) < (D : ℝ) * ‖aVec j‖ * R + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hB : (B j : ℝ) ≤ (D : ℝ) * ‖aVec j‖ * R + 2 := by
        dsimp only [B]; push_cast; linarith
      nlinarith
    calc (∑ j : Fin M, (2 * (B j : ℝ) + 1)) + 1
        ≤ (∑ j : Fin M, (2 * (D : ℝ) * ‖aVec j‖ + 5) * R) + 1 * R := by
          have hs : (∑ j : Fin M, (2 * (B j : ℝ) + 1)) ≤
              ∑ j : Fin M, (2 * (D : ℝ) * ‖aVec j‖ + 5) * R :=
            Finset.sum_le_sum fun j _ => hterm j
          linarith
      _ = C_H * R := by
          dsimp only [C_H]
          rw [← Finset.sum_mul]
          ring
  have hSP : (S.card : ℝ) ≤ ((L.length : ℝ) + 1) ^ r := by
    have := le_trans hS_le_P hP_le
    exact_mod_cast this
  exact le_trans hSP (pow_le_pow_left₀ (by positivity) hL_len r)

/-! ### Section 4: Clamped McShane-Whitney extension and polyhedra -/

private lemma abs_max_sub_max_le (a b c d : ℝ) :
    |max a b - max c d| ≤ max |a - c| |b - d| := by
  have hac : a - c ≤ max |a - c| |b - d| := le_trans (le_abs_self _) (le_max_left _ _)
  have hca : c - a ≤ max |a - c| |b - d| := by
    simpa [abs_sub_comm] using le_trans (le_abs_self (c - a)) (le_max_left |c - a| |b - d|)
  have hbd : b - d ≤ max |a - c| |b - d| := le_trans (le_abs_self _) (le_max_right _ _)
  have hdb : d - b ≤ max |a - c| |b - d| := by
    simpa [abs_sub_comm] using le_trans (le_abs_self (d - b)) (le_max_right |a - c| |d - b|)
  rw [abs_sub_le_iff]
  constructor
  · have h1 : max a b ≤ max c d + max |a - c| |b - d| :=
      max_le (by linarith [le_max_left c d]) (by linarith [le_max_right c d])
    linarith
  · have h2 : max c d ≤ max a b + max |a - c| |b - d| :=
      max_le (by linarith [le_max_left a b]) (by linarith [le_max_right a b])
    linarith

private lemma abs_min_sub_min_le (a b c d : ℝ) :
    |min a b - min c d| ≤ max |a - c| |b - d| := by
  have hac : a - c ≤ max |a - c| |b - d| := le_trans (le_abs_self _) (le_max_left _ _)
  have hca : c - a ≤ max |a - c| |b - d| := by
    simpa [abs_sub_comm] using le_trans (le_abs_self (c - a)) (le_max_left |c - a| |b - d|)
  have hbd : b - d ≤ max |a - c| |b - d| := le_trans (le_abs_self _) (le_max_right _ _)
  have hdb : d - b ≤ max |a - c| |b - d| := by
    simpa [abs_sub_comm] using le_trans (le_abs_self (d - b)) (le_max_right |a - c| |d - b|)
  rw [abs_sub_le_iff]
  constructor
  · have h1 : min a b - max |a - c| |b - d| ≤ min c d :=
      le_min (by linarith [min_le_left a b]) (by linarith [min_le_right a b])
    linarith
  · have h2 : min c d - max |a - c| |b - d| ≤ min a b :=
      le_min (by linarith [min_le_left c d]) (by linarith [min_le_right c d])
    linarith

private lemma exists_clamped_lipschitz_ext {s : ℕ} {A : Set (EuclideanSpace ℝ (Fin s))}
    (hAne : A.Nonempty) (f : EuclideanSpace ℝ (Fin s) → ℝ)
    {L₀ M_f B_A : ℝ} (hL₀ : 0 ≤ L₀) (hMf : 0 < M_f)
    (hlip : ∀ ξ ∈ A, ∀ ζ ∈ A, |f ξ - f ζ| ≤ L₀ * ‖ξ - ζ‖)
    (hbound : ∀ ξ ∈ A, |f ξ| ≤ M_f * max 1 ‖ξ‖)
    (hbdd : ∀ ζ ∈ A, -B_A ≤ f ζ) :
    ∃ g : EuclideanSpace ℝ (Fin s) → ℝ,
      (∀ ξ ∈ A, g ξ = f ξ) ∧
      (∀ ξ₁ ξ₂, |g ξ₁ - g ξ₂| ≤ max L₀ M_f * ‖ξ₁ - ξ₂‖) ∧
      (∀ ξ, |g ξ| ≤ M_f * max 1 ‖ξ‖) := by
  let fExt : EuclideanSpace ℝ (Fin s) → ℝ := fun ξ =>
    sInf ((fun ζ => f ζ + L₀ * ‖ξ - ζ‖) '' A)
  have hBddBelow : ∀ ξ, BddBelow ((fun ζ => f ζ + L₀ * ‖ξ - ζ‖) '' A) := by
    intro ξ
    refine ⟨-B_A, ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    have : 0 ≤ L₀ * ‖ξ - ζ‖ := mul_nonneg hL₀ (norm_nonneg _)
    linarith [hbdd ζ hζ]
  have hfExt_eq : ∀ ξ ∈ A, fExt ξ = f ξ := by
    intro ξ hξ
    apply le_antisymm
    · have hmem : f ξ ∈ (fun ζ => f ζ + L₀ * ‖ξ - ζ‖) '' A :=
        ⟨ξ, hξ, by simp⟩
      exact csInf_le (hBddBelow ξ) hmem
    · refine le_csInf (hAne.image _) ?_
      rintro _ ⟨ζ, hζ, rfl⟩
      have := (abs_sub_le_iff.mp (hlip ξ hξ ζ hζ)).1
      linarith
  have hfExt_lip : ∀ ξ₁ ξ₂, |fExt ξ₁ - fExt ξ₂| ≤ L₀ * ‖ξ₁ - ξ₂‖ := by
    have hone : ∀ ξ₁ ξ₂, fExt ξ₁ - fExt ξ₂ ≤ L₀ * ‖ξ₁ - ξ₂‖ := by
      intro ξ₁ ξ₂
      have hle : fExt ξ₁ - L₀ * ‖ξ₁ - ξ₂‖ ≤ fExt ξ₂ := by
        refine le_csInf (hAne.image _) ?_
        rintro _ ⟨ζ, hζ, rfl⟩
        have h1 : fExt ξ₁ ≤ f ζ + L₀ * ‖ξ₁ - ζ‖ :=
          csInf_le (hBddBelow ξ₁) ⟨ζ, hζ, rfl⟩
        have htri : ‖ξ₁ - ζ‖ ≤ ‖ξ₁ - ξ₂‖ + ‖ξ₂ - ζ‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le (ξ₁ - ξ₂) (ξ₂ - ζ)
        have h2 : L₀ * ‖ξ₁ - ζ‖ ≤ L₀ * ‖ξ₁ - ξ₂‖ + L₀ * ‖ξ₂ - ζ‖ := by
          calc L₀ * ‖ξ₁ - ζ‖ ≤ L₀ * (‖ξ₁ - ξ₂‖ + ‖ξ₂ - ζ‖) := mul_le_mul_of_nonneg_left htri hL₀
            _ = L₀ * ‖ξ₁ - ξ₂‖ + L₀ * ‖ξ₂ - ζ‖ := mul_add _ _ _
        linarith
      linarith
    intro ξ₁ ξ₂
    rw [abs_sub_le_iff]
    exact ⟨hone ξ₁ ξ₂, by simpa [norm_sub_rev] using hone ξ₂ ξ₁⟩
  let b : EuclideanSpace ℝ (Fin s) → ℝ := fun ξ => M_f * max 1 ‖ξ‖
  have hb_lip : ∀ ξ₁ ξ₂, |b ξ₁ - b ξ₂| ≤ M_f * ‖ξ₁ - ξ₂‖ := by
    intro ξ₁ ξ₂
    dsimp only [b]
    rw [← mul_sub, abs_mul, abs_of_pos hMf]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hMf)
    calc |max (1 : ℝ) ‖ξ₁‖ - max 1 ‖ξ₂‖|
        ≤ max |1 - (1 : ℝ)| |‖ξ₁‖ - ‖ξ₂‖| := abs_max_sub_max_le 1 ‖ξ₁‖ 1 ‖ξ₂‖
      _ = |‖ξ₁‖ - ‖ξ₂‖| := by simp
      _ ≤ ‖ξ₁ - ξ₂‖ := abs_norm_sub_norm_le ξ₁ ξ₂
  let g : EuclideanSpace ℝ (Fin s) → ℝ := fun ξ => max (-b ξ) (min (b ξ) (fExt ξ))
  refine ⟨g, ?_, ?_, ?_⟩
  · intro ξ hξ
    dsimp only [g, b]
    rw [hfExt_eq ξ hξ]
    have habs := abs_le.mp (hbound ξ hξ)
    rw [min_eq_right habs.2, max_eq_right habs.1]
  · intro ξ₁ ξ₂
    dsimp only [g]
    have h1 := abs_max_sub_max_le (-b ξ₁) (min (b ξ₁) (fExt ξ₁)) (-b ξ₂) (min (b ξ₂) (fExt ξ₂))
    have h2 := abs_min_sub_min_le (b ξ₁) (fExt ξ₁) (b ξ₂) (fExt ξ₂)
    have hneg : |-b ξ₁ - -b ξ₂| = |b ξ₁ - b ξ₂| := by
      rw [show -b ξ₁ - -b ξ₂ = -(b ξ₁ - b ξ₂) by ring, abs_neg]
    have hL : |fExt ξ₁ - fExt ξ₂| ≤ max L₀ M_f * ‖ξ₁ - ξ₂‖ :=
      le_trans (hfExt_lip ξ₁ ξ₂) (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hM : |b ξ₁ - b ξ₂| ≤ max L₀ M_f * ‖ξ₁ - ξ₂‖ :=
      le_trans (hb_lip ξ₁ ξ₂) (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    calc |max (-b ξ₁) (min (b ξ₁) (fExt ξ₁)) - max (-b ξ₂) (min (b ξ₂) (fExt ξ₂))|
        ≤ max |b ξ₁ - b ξ₂| |min (b ξ₁) (fExt ξ₁) - min (b ξ₂) (fExt ξ₂)| := by rwa [← hneg]
      _ ≤ max (max L₀ M_f * ‖ξ₁ - ξ₂‖) (max |b ξ₁ - b ξ₂| |fExt ξ₁ - fExt ξ₂|) :=
          max_le_max hM h2
      _ ≤ max L₀ M_f * ‖ξ₁ - ξ₂‖ := max_le le_rfl (max_le hM hL)
  · intro ξ
    dsimp only [g, b]
    have hbn : 0 ≤ M_f * max 1 ‖ξ‖ := mul_nonneg (le_of_lt hMf) (le_trans zero_le_one (le_max_left _ _))
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private lemma polyAtMost_inter {s k₁ k₂ : ℕ} {P₁ P₂ : Set (EuclideanSpace ℝ (Fin s))}
    (h₁ : P₁ ∈ PolyAtMost s k₁) (h₂ : P₂ ∈ PolyAtMost s k₂) :
    P₁ ∩ P₂ ∈ PolyAtMost s (k₁ + k₂) := by
  obtain ⟨a₁, b₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, rfl⟩ := h₂
  refine ⟨Fin.addCases a₁ a₂, Fin.addCases b₁ b₂, ?_⟩
  ext ξ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
    · simpa using h1 i₁
    · simpa using h2 i₂
  · intro h
    refine ⟨fun i₁ => ?_, fun i₂ => ?_⟩
    · simpa using h (Fin.castAdd k₂ i₁)
    · simpa using h (Fin.natAdd k₁ i₂)

private lemma box_mem_polyAtMost {s : ℕ} (ρ : ℝ) :
    {ξ : EuclideanSpace ℝ (Fin s) | ∀ i : Fin s, |ξ i| ≤ ρ} ∈ PolyAtMost s (s + s) := by
  refine ⟨Fin.addCases (fun i => EuclideanSpace.single i 1) (fun i => EuclideanSpace.single i (-1)),
    fun _ => ρ, ?_⟩
  ext ξ
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left, EuclideanSpace.inner_single_left, conj_trivial, one_mul]
      exact (abs_le.mp (h j)).2
    · simp only [Fin.addCases_right, EuclideanSpace.inner_single_left, conj_trivial, neg_mul,
        one_mul]
      linarith [(abs_le.mp (h j)).1]
  · intro h j
    have h1 := h (Fin.castAdd s j)
    have h2 := h (Fin.natAdd s j)
    simp only [Fin.addCases_left, Fin.addCases_right, EuclideanSpace.inner_single_left,
      conj_trivial, one_mul, neg_mul] at h1 h2
    exact abs_le.mpr ⟨by linarith, h1⟩

private lemma affine_halfspaces_mem_polyAtMost {s M : ℕ}
    (ℓ : Fin M → (EuclideanSpace ℝ (Fin s) →ₗ[ℝ] ℝ)) (v : Fin M → ℝ) (c : Fin M → ℝ) :
    {ξ : EuclideanSpace ℝ (Fin s) | ∀ j : Fin M, ℓ j ξ + v j ≤ c j} ∈ PolyAtMost s M := by
  let a : Fin M → EuclideanSpace ℝ (Fin s) := fun j =>
    WithLp.toLp 2 (fun l => ℓ j (EuclideanSpace.single l (1 : ℝ)))
  refine ⟨a, fun j => c j - v j, ?_⟩
  ext ξ
  simp only [Set.mem_ofPred_eq]
  refine forall_congr' fun j => ?_
  have hinner : inner ℝ (a j) ξ = ℓ j ξ := by
    have hdecomp : ξ = ∑ l : Fin s, (ξ l) • EuclideanSpace.single l (1 : ℝ) := by
      apply WithLp.ofLp_injective 2
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc inner ℝ (a j) ξ
        = ∑ l : Fin s, ξ l * ℓ j (EuclideanSpace.single l (1 : ℝ)) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]
          simp only [star_trivial, dotProduct, a]
      _ = ℓ j (∑ l : Fin s, (ξ l) • EuclideanSpace.single l (1 : ℝ)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ℓ j ξ := by rw [← hdecomp]
  rw [hinner]
  constructor <;> intro h <;> linarith

private lemma polyAtMost_isClosed {s k : ℕ} {P : Set (EuclideanSpace ℝ (Fin s))}
    (hP : P ∈ PolyAtMost s k) : IsClosed P := by
  obtain ⟨a, b, rfl⟩ := hP
  have : {ξ : EuclideanSpace ℝ (Fin s) | ∀ i : Fin k, inner ℝ (a i) ξ ≤ b i} =
      ⋂ i : Fin k, {ξ | inner ℝ (a i) ξ ≤ b i} := by
    ext ξ; simp
  rw [this]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

private lemma indicator_inclusion_exclusion {α : Type*} {M : ℕ}
    (E : Set α) (ψ : Fin M → α → ℝ) (κ : Fin M → ℤ) (g : α → ℝ) :
    ∀ ξ : α,
      ({ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < ψ j ξ ∧ ψ j ξ ≤ (κ j : ℝ)}).indicator g ξ =
      ∑ S : Finset (Fin M), ((-1 : ℝ) ^ S.card) *
        ({ξ | ξ ∈ E ∧ ∀ j : Fin M,
          ψ j ξ ≤ (κ j : ℝ) - (if j ∈ S then (1 : ℝ) else 0)}).indicator g ξ := by
  classical
  let Aset : Set α := {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < ψ j ξ ∧ ψ j ξ ≤ (κ j : ℝ)}
  let Pset : Finset (Fin M) → Set α := fun S =>
    {ξ | ξ ∈ E ∧ ∀ j : Fin M, ψ j ξ ≤ (κ j : ℝ) - (if j ∈ S then (1 : ℝ) else 0)}
  intro ξ
  change Aset.indicator g ξ = ∑ S : Finset (Fin M), ((-1 : ℝ) ^ S.card) * (Pset S).indicator g ξ
  by_cases hbase : ξ ∈ E ∧ ∀ j : Fin M, ψ j ξ ≤ (κ j : ℝ)
  · let T : Finset (Fin M) := Finset.univ.filter (fun j => ψ j ξ ≤ (κ j : ℝ) - 1)
    have hmem_S : ∀ S : Finset (Fin M), ξ ∈ Pset S ↔ S ⊆ T := by
      intro S
      constructor
      · intro ⟨_, hS⟩ j hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [hj] using hS j
      · intro hST
        refine ⟨hbase.1, fun j => ?_⟩
        by_cases hj : j ∈ S
        · simpa [hj] using (Finset.mem_filter.mp (hST hj)).2
        · simpa [hj] using hbase.2 j
    have hsum : (∑ S : Finset (Fin M), ((-1 : ℝ) ^ S.card) * (Pset S).indicator g ξ) =
        (∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card) * g ξ := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_subset (Finset.subset_univ T.powerset)]
      · refine Finset.sum_congr rfl fun S hS => ?_
        have hST : S ⊆ T := Finset.mem_powerset.mp hS
        rw [Set.indicator_of_mem ((hmem_S S).mpr hST)]
      · intro S _ hnot
        have hnot' : ¬ S ⊆ T := fun h => hnot (Finset.mem_powerset.mpr h)
        rw [Set.indicator_of_notMem (fun hm => hnot' ((hmem_S S).mp hm)), mul_zero]
    rw [hsum]
    have hpow : (∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card) = if T = ∅ then (1 : ℝ) else 0 := by
      have hZ := Finset.sum_powerset_neg_one_pow_card (x := T)
      have hR := congr_arg (Int.cast : ℤ → ℝ) hZ
      simpa using hR
    rw [hpow]
    have hiff_T : ξ ∈ Aset ↔ T = ∅ := by
      constructor
      · intro ⟨_, hlt⟩
        ext j
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_le]
        exact (hlt j).1
      · intro hTe
        refine ⟨hbase.1, fun j => ⟨?_, hbase.2 j⟩⟩
        by_contra hle
        push Not at hle
        have : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
        rw [hTe] at this
        exact Finset.notMem_empty _ this
    by_cases hT : T = ∅
    · rw [Set.indicator_of_mem (hiff_T.mpr hT), if_pos hT, one_mul]
    · rw [Set.indicator_of_notMem (fun h => hT (hiff_T.mp h)), if_neg hT, zero_mul]
  · have hnmem : ξ ∉ Aset := fun ⟨hE, hall⟩ => hbase ⟨hE, fun j => (hall j).2⟩
    rw [Set.indicator_of_notMem hnmem]
    symm
    apply Finset.sum_eq_zero
    intro S _
    have hnot : ξ ∉ Pset S := by
      rintro ⟨hE, hall⟩
      apply hbase
      refine ⟨hE, fun j => ?_⟩
      have hj := hall j
      split_ifs at hj <;> linarith
    rw [Set.indicator_of_notMem hnot, mul_zero]

/-! ### Section 5: Measure theory, moments, and expectation bridge -/

private lemma rpow_p_integrable_of_PpK {s : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin s))}
    {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    {ν : Measure (EuclideanSpace ℝ (Fin s))} (hν : ν ∈ PpK Ξ p K) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => ‖ξ‖ ^ p) ν ∧
    (∫ ξ, ‖ξ‖ ^ p ∂ν) ≤ K ∧
    Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => max (1 : ℝ) ‖ξ‖) ν := by
  have hprob : IsProbabilityMeasure ν := hν.1.1.1
  have hlt : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ p) ∂ν < ∞ := hν.1.2
  have hle : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ p) ∂ν ≤ ENNReal.ofReal K := hν.2
  have hcont_p : Continuous (fun ξ : EuclideanSpace ℝ (Fin s) => ‖ξ‖ ^ p) :=
    continuous_norm.rpow_const (fun _ => Or.inr (by linarith))
  have hint_p : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => ‖ξ‖ ^ p) ν := by
    refine ⟨hcont_p.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have heq : (fun ξ : EuclideanSpace ℝ (Fin s) => ‖‖ξ‖ ^ p‖ₑ) =
        fun ξ => ENNReal.ofReal (‖ξ‖ ^ p) := by
      ext ξ
      rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
    rwa [heq]
  have hint_le : (∫ ξ, ‖ξ‖ ^ p ∂ν) ≤ K := by
    have hnn : 0 ≤ᵐ[ν] (fun ξ : EuclideanSpace ℝ (Fin s) => ‖ξ‖ ^ p) :=
      Filter.Eventually.of_forall fun ξ => Real.rpow_nonneg (norm_nonneg _) _
    rw [integral_eq_lintegral_of_nonneg_ae hnn hcont_p.aestronglyMeasurable]
    calc (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ p) ∂ν).toReal
        ≤ (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = K := ENNReal.toReal_ofReal (le_of_lt hK)
  have hint_max : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => max (1 : ℝ) ‖ξ‖) ν := by
    have hdom : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => (1 : ℝ) + ‖ξ‖ ^ p) ν :=
      (integrable_const (1 : ℝ)).add hint_p
    refine hdom.mono' (continuous_const.max continuous_norm).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    have hmax_nn : 0 ≤ max (1 : ℝ) ‖ξ‖ := le_trans zero_le_one (le_max_left _ _)
    rw [Real.norm_of_nonneg hmax_nn]
    rcases le_total (1 : ℝ) ‖ξ‖ with h1 | h1
    · rw [max_eq_right h1]
      have hpow : ‖ξ‖ ≤ ‖ξ‖ ^ p := by
        calc ‖ξ‖ = ‖ξ‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ ‖ξ‖ ^ p := Real.rpow_le_rpow_of_exponent_le h1 (le_of_lt hp)
      linarith
    · rw [max_eq_left h1]
      linarith [Real.rpow_nonneg (norm_nonneg ξ) p]
  exact ⟨hint_p, hint_le, hint_max⟩

private lemma expect_eq_coe_integral {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (g : α → EReal) (f : α → ℝ)
    (hf : Integrable f ν) (hae : ∀ᵐ ξ ∂ν, g ξ = (f ξ : EReal)) :
    DupacovaWets.Consistency.expect ν g = ((∫ ξ, f ξ ∂ν : ℝ) : EReal) := by
  have hpos_ae : (fun ξ => (g ξ).toENNReal) =ᵐ[ν] (fun ξ => ENNReal.ofReal (f ξ)) := by
    filter_upwards [hae] with ξ hξ
    rw [hξ, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have hneg_ae : (fun ξ => (-g ξ).toENNReal) =ᵐ[ν] (fun ξ => ENNReal.ofReal (-f ξ)) := by
    filter_upwards [hae] with ξ hξ
    rw [hξ, ← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have hpos_eq : ∫⁻ ξ, (g ξ).toENNReal ∂ν = ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂ν :=
    lintegral_congr_ae hpos_ae
  have hneg_eq : ∫⁻ ξ, (-g ξ).toENNReal ∂ν = ∫⁻ ξ, ENNReal.ofReal (-f ξ) ∂ν :=
    lintegral_congr_ae hneg_ae
  have hpos_lt : ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂ν < ∞ := by
    refine lt_of_le_of_lt ?_ hf.hasFiniteIntegral
    refine lintegral_mono fun ξ => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (f ξ))
  have hneg_lt : ∫⁻ ξ, ENNReal.ofReal (-f ξ) ∂ν < ∞ := by
    refine lt_of_le_of_lt ?_ hf.hasFiniteIntegral
    refine lintegral_mono fun ξ => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs (f ξ))
  unfold DupacovaWets.Consistency.expect
  rw [hpos_eq, hneg_eq, if_neg (ne_of_lt hpos_lt)]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have hp_coe : ((∫⁻ ξ, ENNReal.ofReal (f ξ) ∂ν : ℝ≥0∞) : EReal) =
      (((∫⁻ ξ, ENNReal.ofReal (f ξ) ∂ν).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal (ne_of_lt hpos_lt)]
  have hn_coe : ((∫⁻ ξ, ENNReal.ofReal (-f ξ) ∂ν : ℝ≥0∞) : EReal) =
      (((∫⁻ ξ, ENNReal.ofReal (-f ξ) ∂ν).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal (ne_of_lt hneg_lt)]
  rw [hp_coe, hn_coe, ← EReal.coe_sub]

private lemma measurable_indicator_f0 {m s r mh mb : ℕ} (P : MIProgram m s r mh mb)
    (hΞ_closed : IsClosed P.Ξ) (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ P.X) :
    Measurable (P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)) := by
  have h35b := ProbMetricStab.MixedInt.lemma_3_5_b P.recourse hB1 hB3
  have hfin := h35b.1
  have hlsc := h35b.2.1
  let g : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin r) := fun ξ => P.h ξ - P.T ξ x
  have hg_cont : Continuous g := by
    have hh : Continuous P.h := P.h.continuous_of_finiteDimensional
    have hT : Continuous P.T := P.T.continuous_of_finiteDimensional
    have hev : Continuous (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r) => L x) :=
      ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin r)) x |>.continuous
    exact hh.sub (hev.comp hT)
  have hsublevel_closed : ∀ a : ℝ, IsClosed {ξ ∈ P.Ξ | (P.f0 ξ x).toReal ≤ a} := by
    intro a
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro ξ hξ
    by_cases hξΞ : ξ ∈ P.Ξ
    · have hgt : a < (P.f0 ξ x).toReal := by
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le] at hξ
        exact hξ hξΞ
      have hgt_phi : ((a - inner ℝ P.c x : ℝ) : EReal) < P.recourse.Phi (g ξ) := by
        have ht := hB2 ξ hξΞ x hx
        have hft := hfin (g ξ) ht
        have hf0_toReal : (P.f0 ξ x).toReal = inner ℝ P.c x + (P.recourse.Phi (g ξ)).toReal := by
          change (((inner ℝ P.c x : ℝ) : EReal) + P.recourse.Phi (g ξ)).toReal = _
          rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hft.1 hft.2,
            EReal.toReal_coe]
        rw [← EReal.coe_toReal hft.1 hft.2]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      have hnhds := hlsc (g ξ) (hB2 ξ hξΞ x hx) ((a - inner ℝ P.c x : ℝ) : EReal) hgt_phi
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnhds
      obtain ⟨ε, hε, hball⟩ := hnhds
      have hpre : IsOpen (g ⁻¹' Metric.ball (g ξ) ε) :=
        Metric.isOpen_ball.preimage hg_cont
      refine ⟨g ⁻¹' Metric.ball (g ξ) ε, ?_, hpre, Metric.mem_ball_self hε⟩
      intro ξ' hξ'
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le]
      intro hξ'Ξ
      have ht' := hB2 ξ' hξ'Ξ x hx
      have hft' := hfin (g ξ') ht'
      have hphi_gt : ((a - inner ℝ P.c x : ℝ) : EReal) < P.recourse.Phi (g ξ') :=
        hball (Metric.mem_ball.mp hξ') ht'
      rw [← EReal.coe_toReal hft'.1 hft'.2] at hphi_gt
      have hreal_gt := EReal.coe_lt_coe_iff.mp hphi_gt
      have hf0_toReal' : (P.f0 ξ' x).toReal = inner ℝ P.c x + (P.recourse.Phi (g ξ')).toReal := by
        change (((inner ℝ P.c x : ℝ) : EReal) + P.recourse.Phi (g ξ')).toReal = _
        rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hft'.1 hft'.2,
          EReal.toReal_coe]
      linarith
    · refine ⟨P.Ξᶜ, ?_, hΞ_closed.isOpen_compl, hξΞ⟩
      intro ξ' hξ' hmem
      exact hξ' hmem.1
  apply measurable_of_Iic
  intro a
  by_cases ha : 0 ≤ a
  · have heq : (P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)) ⁻¹' Set.Iic a =
        P.Ξᶜ ∪ {ξ ∈ P.Ξ | (P.f0 ξ x).toReal ≤ a} := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
      by_cases hξ : ξ ∈ P.Ξ
      · simp [hξ]
      · simp [hξ, ha]
    rw [heq]
    exact hΞ_closed.measurableSet.compl.union (hsublevel_closed a).measurableSet
  · have heq : (P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)) ⁻¹' Set.Iic a =
        {ξ ∈ P.Ξ | (P.f0 ξ x).toReal ≤ a} := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
      by_cases hξ : ξ ∈ P.Ξ
      · simp [hξ]
      · simp [hξ, ha]
    rw [heq]
    exact (hsublevel_closed a).measurableSet

/-! ### Tail bound and ρ-optimization helpers -/

private lemma tail_bound_one {s : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin s))}
    (hΞ_meas : MeasurableSet Ξ) {p K M_f ρ : ℝ}
    (hp : 1 < p) (hMf_pos : 0 < M_f) (hρ : 1 ≤ ρ)
    {F : EuclideanSpace ℝ (Fin s) → ℝ}
    (hF_zero : ∀ ξ ∉ Ξ, F ξ = 0)
    (hF_bound : ∀ ξ, ‖F ξ‖ ≤ M_f * max 1 ‖ξ‖)
    {η : Measure (EuclideanSpace ℝ (Fin s))}
    (hF_int : Integrable F η)
    (hη_p : Integrable (fun ξ => ‖ξ‖ ^ p) η)
    (hη_K : (∫ ξ, ‖ξ‖ ^ p ∂η) ≤ K) :
    |∫ ξ in (Ξ ∩ {ξ : EuclideanSpace ℝ (Fin s) | ∀ i : Fin s, |ξ i| ≤ ρ})ᶜ, F ξ ∂η| ≤
      M_f * K * ρ ^ (-(p - 1)) := by
  let Qρ : Set (EuclideanSpace ℝ (Fin s)) := {ξ | ∀ i : Fin s, |ξ i| ≤ ρ}
  have hQρ_meas : MeasurableSet Qρ := (polyAtMost_isClosed (box_mem_polyAtMost ρ)).measurableSet
  have hΞQ_meas : MeasurableSet (Ξ ∩ Qρ) := hΞ_meas.inter hQρ_meas
  have hdom : ∀ ξ ∈ (Ξ ∩ Qρ)ᶜ, ‖F ξ‖ ≤ M_f * ρ ^ (-(p - 1)) * ‖ξ‖ ^ p := by
    intro ξ hξ
    by_cases hξΞ : ξ ∈ Ξ
    · have hnotQ : ξ ∉ Qρ := fun hQ => hξ ⟨hξΞ, hQ⟩
      simp only [Qρ, Set.mem_ofPred_eq, not_forall, not_le] at hnotQ
      obtain ⟨i₀, hi₀⟩ := hnotQ
      have hnorm_gt : ρ < ‖ξ‖ := by
        have hcoord : |ξ i₀| ≤ ‖ξ‖ := by
          have : ‖ξ i₀‖ ≤ ‖ξ‖ := PiLp.norm_apply_le ξ i₀
          simpa [Real.norm_eq_abs] using this
        linarith
      have hnorm_gt1 : 1 ≤ ‖ξ‖ := le_trans hρ (le_of_lt hnorm_gt)
      have hmax : max (1 : ℝ) ‖ξ‖ = ‖ξ‖ := max_eq_right hnorm_gt1
      have hrpow : ρ ^ (p - 1) ≤ ‖ξ‖ ^ (p - 1) :=
        Real.rpow_le_rpow (by linarith) (le_of_lt hnorm_gt) (by linarith)
      have hmul : ‖ξ‖ = ρ ^ (-(p - 1)) * (ρ ^ (p - 1) * ‖ξ‖) := by
        rw [← mul_assoc, ← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero, one_mul]
      have hpow_le : ρ ^ (p - 1) * ‖ξ‖ ≤ ‖ξ‖ ^ p := by
        calc ρ ^ (p - 1) * ‖ξ‖
            ≤ ‖ξ‖ ^ (p - 1) * ‖ξ‖ := mul_le_mul_of_nonneg_right hrpow (norm_nonneg _)
          _ = ‖ξ‖ ^ (p - 1) * ‖ξ‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = ‖ξ‖ ^ p := by rw [← Real.rpow_add (by linarith)]; ring_nf
      have hF_le : ‖F ξ‖ ≤ M_f * ‖ξ‖ := by
        simpa [hmax] using hF_bound ξ
      calc ‖F ξ‖ ≤ M_f * ‖ξ‖ := hF_le
        _ = M_f * (ρ ^ (-(p - 1)) * (ρ ^ (p - 1) * ‖ξ‖)) := by rw [← hmul]
        _ ≤ M_f * (ρ ^ (-(p - 1)) * ‖ξ‖ ^ p) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpow_le (Real.rpow_nonneg (by linarith) _))
              (le_of_lt hMf_pos)
        _ = M_f * ρ ^ (-(p - 1)) * ‖ξ‖ ^ p := by ring
    · rw [hF_zero ξ hξΞ, norm_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hMf_pos) (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (norm_nonneg _) _)
  have h1 : |∫ ξ in (Ξ ∩ Qρ)ᶜ, F ξ ∂η| ≤ ∫ ξ in (Ξ ∩ Qρ)ᶜ, ‖F ξ‖ ∂η := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := F) (μ := η.restrict (Ξ ∩ Qρ)ᶜ)
  have h2 : ∫ ξ in (Ξ ∩ Qρ)ᶜ, ‖F ξ‖ ∂η ≤
      ∫ ξ in (Ξ ∩ Qρ)ᶜ, M_f * ρ ^ (-(p - 1)) * ‖ξ‖ ^ p ∂η :=
    setIntegral_mono_on hF_int.norm.integrableOn
      (hη_p.const_mul (M_f * ρ ^ (-(p - 1)))).integrableOn hΞQ_meas.compl hdom
  have h3 : ∫ ξ in (Ξ ∩ Qρ)ᶜ, M_f * ρ ^ (-(p - 1)) * ‖ξ‖ ^ p ∂η ≤
      ∫ ξ, M_f * ρ ^ (-(p - 1)) * ‖ξ‖ ^ p ∂η :=
    setIntegral_le_integral (hη_p.const_mul (M_f * ρ ^ (-(p - 1)))) (Filter.Eventually.of_forall fun ξ =>
      mul_nonneg (mul_nonneg (le_of_lt hMf_pos) (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ρ) _))
        (Real.rpow_nonneg (norm_nonneg _) _))
  have h4 : ∫ ξ, M_f * ρ ^ (-(p - 1)) * ‖ξ‖ ^ p ∂η ≤ M_f * K * ρ ^ (-(p - 1)) := by
    rw [integral_const_mul]
    have hc_nn : 0 ≤ M_f * ρ ^ (-(p - 1)) :=
      mul_nonneg (le_of_lt hMf_pos) (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ρ) _)
    have := mul_le_mul_of_nonneg_left hη_K hc_nn
    linarith
  exact le_trans (le_trans (le_trans h1 h2) h3) h4

private lemma optimize_rho_bound {r : ℕ} {p C_A C_B Dval val : ℝ}
    (hp : 1 < p) (hCA_pos : 0 < C_A) (hCB_pos : 0 < C_B)
    (hDval_nn : 0 ≤ Dval) (hDval_lt1 : Dval < 1) (hval_nn : 0 ≤ val)
    (hrho : ∀ ρ : ℝ, 1 ≤ ρ → val ≤ C_A * ρ ^ r * Dval + C_B * ρ ^ (-(p - 1))) :
    val ≤ (C_A + C_B) * Dval ^ (1 / (1 + (r : ℝ) / (p - 1))) := by
  let e : ℝ := 1 / (1 + (r : ℝ) / (p - 1))
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hden_pos : 0 < (r : ℝ) + (p - 1) := by positivity
  have he_eq : e = (p - 1) / ((r : ℝ) + (p - 1)) := by
    dsimp only [e]
    field_simp [ne_of_gt hp1, ne_of_gt hden_pos]
    ring
  rcases eq_or_lt_of_le hDval_nn with hD0 | hDpos
  · have hzero : val = 0 := by
      by_contra hne
      have hpos : 0 < val := lt_of_le_of_ne hval_nn (Ne.symm hne)
      let ρ := max (1 : ℝ) ((2 * C_B / val) ^ (1 / (p - 1)))
      have hρ1 : 1 ≤ ρ := le_max_left _ _
      have hρ2 : (2 * C_B / val) ^ (1 / (p - 1)) ≤ ρ := le_max_right _ _
      have hρ_pow : 2 * C_B / val ≤ ρ ^ (p - 1) := by
        calc 2 * C_B / val
            = ((2 * C_B / val) ^ (1 / (p - 1))) ^ (p - 1) := by
              rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hp1), Real.rpow_one]
          _ ≤ ρ ^ (p - 1) :=
              Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hρ2 (le_of_lt hp1)
      have hinv : C_B * ρ ^ (-(p - 1)) ≤ val / 2 := by
        rw [Real.rpow_neg (by linarith)]
        have h1 : (ρ ^ (p - 1))⁻¹ ≤ (2 * C_B / val)⁻¹ :=
          inv_anti₀ (by positivity) hρ_pow
        have h2 : C_B * (2 * C_B / val)⁻¹ = val / 2 := by
          field_simp [ne_of_gt hCB_pos, ne_of_gt hpos]
        calc C_B * (ρ ^ (p - 1))⁻¹ ≤ C_B * (2 * C_B / val)⁻¹ :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hCB_pos)
          _ = val / 2 := h2
      have hbd := hrho ρ hρ1
      rw [← hD0, mul_zero, zero_add] at hbd
      linarith
    rw [hzero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hDval_nn _)
  · let ρ : ℝ := Dval ^ (-(1 / ((r : ℝ) + (p - 1))))
    have hρ1 : 1 ≤ ρ := by
      dsimp only [ρ]
      rw [Real.rpow_neg (le_of_lt hDpos)]
      have hle1 : Dval ^ (1 / ((r : ℝ) + (p - 1))) ≤ 1 :=
        Real.rpow_le_one (le_of_lt hDpos) (le_of_lt hDval_lt1) (by positivity)
      exact (one_le_inv₀ (Real.rpow_pos_of_pos hDpos _)).mpr hle1
    have htermA : ρ ^ r * Dval = Dval ^ e := by
      dsimp only [ρ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hDpos)]
      conv_lhs => rhs; rw [← Real.rpow_one Dval]
      rw [← Real.rpow_add hDpos, he_eq]
      congr 1
      field_simp [ne_of_gt hden_pos]
      ring
    have htermB : ρ ^ (-(p - 1)) = Dval ^ e := by
      dsimp only [ρ]
      rw [← Real.rpow_mul (le_of_lt hDpos), he_eq]
      congr 1
      field_simp [ne_of_gt hden_pos]
    calc val ≤ C_A * ρ ^ r * Dval + C_B * ρ ^ (-(p - 1)) := hrho ρ hρ1
      _ = C_A * (ρ ^ r * Dval) + C_B * ρ ^ (-(p - 1)) := by ring
      _ = C_A * Dval ^ e + C_B * Dval ^ e := by rw [htermA, htermB]
      _ = (C_A + C_B) * Dval ^ e := by ring

private lemma core_cell_bound {s M kE : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin s))} (hE_poly : E ∈ PolyAtMost s kE)
    (ℓψ : Fin M → (EuclideanSpace ℝ (Fin s) →ₗ[ℝ] ℝ)) (vψ : Fin M → ℝ) (κ : Fin M → ℤ)
    (F : EuclideanSpace ℝ (Fin s) → ℝ)
    {L₀ M_f B_A : ℝ} (hL₀ : 0 ≤ L₀) (hMf_pos : 0 < M_f)
    {μ ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hμ_int_max : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => max (1 : ℝ) ‖ξ‖) μ)
    (hν_int_max : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => max (1 : ℝ) ‖ξ‖) ν)
    (hd_ne_top : d1phk (kE + M) μ ν ≠ ⊤)
    (hF_lip : ∀ ξ₁ ∈ {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
        (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)},
      ∀ ξ₂ ∈ {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
        (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)},
      |F ξ₁ - F ξ₂| ≤ L₀ * ‖ξ₁ - ξ₂‖)
    (hF_bound : ∀ ξ ∈ {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
        (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)},
      |F ξ| ≤ M_f * max 1 ‖ξ‖)
    (hF_bdd : ∀ ζ ∈ {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
        (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)},
      -B_A ≤ F ζ) :
    |(∫ ξ in {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
        (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)}, F ξ ∂μ) -
      ∫ ξ in {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
        (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)}, F ξ ∂ν| ≤
      (2 : ℝ) ^ M * max L₀ M_f * (d1phk (kE + M) μ ν).toReal := by
  classical
  let ψ : Fin M → EuclideanSpace ℝ (Fin s) → ℝ := fun j ξ => ℓψ j ξ + vψ j
  let Aset : Set (EuclideanSpace ℝ (Fin s)) :=
    {ξ | ξ ∈ E ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < ψ j ξ ∧ ψ j ξ ≤ (κ j : ℝ)}
  let Lstar : ℝ := max L₀ M_f
  have hLstar_pos : 0 < Lstar := lt_of_lt_of_le hMf_pos (le_max_right _ _)
  let Dval : ℝ := (d1phk (kE + M) μ ν).toReal
  have hDval_nn : 0 ≤ Dval := ENNReal.toReal_nonneg
  change |(∫ ξ in Aset, F ξ ∂μ) - ∫ ξ in Aset, F ξ ∂ν| ≤ (2 : ℝ) ^ M * Lstar * Dval
  by_cases hAne : Aset.Nonempty
  · have hE_meas : MeasurableSet E := (polyAtMost_isClosed hE_poly).measurableSet
    have hψ_cont : ∀ j, Continuous (ψ j) := fun j =>
      ((ℓψ j).continuous_of_finiteDimensional).add continuous_const
    have hA_meas : MeasurableSet Aset := by
      have heq : Aset = E ∩ ⋂ j : Fin M,
          ({ξ | ((κ j : ℝ) - 1) < ψ j ξ} ∩ {ξ | ψ j ξ ≤ (κ j : ℝ)}) := by
        ext ξ; simp [Aset]
      rw [heq]
      refine hE_meas.inter (MeasurableSet.iInter fun j => ?_)
      exact (isOpen_lt continuous_const (hψ_cont j)).measurableSet.inter
        (isClosed_le (hψ_cont j) continuous_const).measurableSet
    obtain ⟨gExt, hgExt_eq, hgExt_lip, hgExt_bound⟩ :=
      exists_clamped_lipschitz_ext hAne F hL₀ hMf_pos hF_lip hF_bound hF_bdd
    have hgExt_cont : Continuous gExt := by
      rw [Metric.continuous_iff]
      intro ξ ε hε
      refine ⟨ε / Lstar, div_pos hε hLstar_pos, fun ξ' hdist => ?_⟩
      have := hgExt_lip ξ' ξ
      rw [Real.dist_eq]
      calc |gExt ξ' - gExt ξ| ≤ Lstar * ‖ξ' - ξ‖ := this
        _ < Lstar * (ε / Lstar) := by
            apply mul_lt_mul_of_pos_left _ hLstar_pos
            simpa [dist_eq_norm] using hdist
        _ = ε := mul_div_cancel₀ _ (ne_of_gt hLstar_pos)
    have hgExt_int_μ : Integrable gExt μ :=
      (hμ_int_max.const_mul M_f).mono' hgExt_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => by simpa [Real.norm_eq_abs] using hgExt_bound ξ)
    have hgExt_int_ν : Integrable gExt ν :=
      (hν_int_max.const_mul M_f).mono' hgExt_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => by simpa [Real.norm_eq_abs] using hgExt_bound ξ)
    let Pset : Finset (Fin M) → Set (EuclideanSpace ℝ (Fin s)) := fun S =>
      {ξ | ξ ∈ E ∧ ∀ j : Fin M, ψ j ξ ≤ (κ j : ℝ) - (if j ∈ S then (1 : ℝ) else 0)}
    have hPset_poly : ∀ S : Finset (Fin M), Pset S ∈ PolyAtMost s (kE + M) := by
      intro S
      have hH_poly : {ξ | ∀ j : Fin M,
          ψ j ξ ≤ (κ j : ℝ) - (if j ∈ S then (1 : ℝ) else 0)} ∈ PolyAtMost s M :=
        affine_halfspaces_mem_polyAtMost ℓψ vψ _
      have hPset_eq : Pset S = E ∩ {ξ | ∀ j : Fin M,
          ψ j ξ ≤ (κ j : ℝ) - (if j ∈ S then (1 : ℝ) else 0)} := by
        ext ξ; simp [Pset]
      rw [hPset_eq]
      exact polyAtMost_inter hE_poly hH_poly
    have hPset_meas : ∀ S, MeasurableSet (Pset S) := fun S =>
      (polyAtMost_isClosed (hPset_poly S)).measurableSet
    have hIE_int : ∀ {η : Measure (EuclideanSpace ℝ (Fin s))},
        Integrable gExt η →
        (∫ ξ in Aset, F ξ ∂η) =
        ∑ S : Finset (Fin M), ((-1 : ℝ) ^ S.card) * ∫ ξ in Pset S, gExt ξ ∂η := by
      intro η hg_int
      have heq1 : (∫ ξ in Aset, F ξ ∂η) = ∫ ξ in Aset, gExt ξ ∂η :=
        setIntegral_congr_fun hA_meas (fun ξ hξ => (hgExt_eq ξ hξ).symm)
      rw [heq1, ← integral_indicator hA_meas]
      have hfun_eq : Aset.indicator gExt =
          fun ξ => ∑ S : Finset (Fin M), ((-1 : ℝ) ^ S.card) * (Pset S).indicator gExt ξ := by
        ext ξ
        exact indicator_inclusion_exclusion E ψ κ gExt ξ
      rw [hfun_eq, integral_finsetSum]
      · refine Finset.sum_congr rfl fun S _ => ?_
        rw [integral_const_mul, integral_indicator (hPset_meas S)]
      · intro S _
        exact (hg_int.indicator (hPset_meas S)).const_mul _
    rw [hIE_int hgExt_int_μ, hIE_int hgExt_int_ν, ← Finset.sum_sub_distrib]
    have hS_bound : ∀ S : Finset (Fin M),
        |((-1 : ℝ) ^ S.card) * (∫ ξ in Pset S, gExt ξ ∂μ) -
          ((-1 : ℝ) ^ S.card) * (∫ ξ in Pset S, gExt ξ ∂ν)| ≤ Lstar * Dval := by
      intro S
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      let fScal : EuclideanSpace ℝ (Fin s) → ℝ := fun ξ => Lstar⁻¹ * gExt ξ
      have hfScal_mem : fScal ∈ F1lg (Pset S) := by
        refine ⟨?_, ?_⟩
        · apply LipschitzWith.lipschitzOnWith
          rw [lipschitzWith_iff_dist_le_mul]
          intro ξ₁ ξ₂
          simp only [fScal, NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
          rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hLstar_pos)]
          calc Lstar⁻¹ * |gExt ξ₁ - gExt ξ₂|
              ≤ Lstar⁻¹ * (Lstar * ‖ξ₁ - ξ₂‖) :=
                mul_le_mul_of_nonneg_left (hgExt_lip ξ₁ ξ₂) (inv_nonneg.mpr (le_of_lt hLstar_pos))
            _ = ‖ξ₁ - ξ₂‖ := inv_mul_cancel_left₀ (ne_of_gt hLstar_pos) _
        · intro ξ _
          simp only [fScal, abs_mul, abs_of_pos (inv_pos.mpr hLstar_pos)]
          have hMf_le : M_f ≤ Lstar := le_max_right _ _
          calc Lstar⁻¹ * |gExt ξ|
              ≤ Lstar⁻¹ * (M_f * max 1 ‖ξ‖) :=
                mul_le_mul_of_nonneg_left (hgExt_bound ξ) (inv_nonneg.mpr (le_of_lt hLstar_pos))
            _ ≤ Lstar⁻¹ * (Lstar * max 1 ‖ξ‖) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hMf_le (le_trans zero_le_one (le_max_left _ _)))
                  (inv_nonneg.mpr (le_of_lt hLstar_pos))
            _ = max 1 ‖ξ‖ := inv_mul_cancel_left₀ (ne_of_gt hLstar_pos) _
      have hd_le : ‖(∫ ξ in Pset S, fScal ξ ∂μ) - ∫ ξ in Pset S, fScal ξ ∂ν‖ₑ ≤
          d1phk (kE + M) μ ν :=
        le_iSup₂_of_le (Pset S) (hPset_poly S) (le_iSup₂_of_le fScal hfScal_mem le_rfl)
      rw [Real.enorm_eq_ofReal_abs] at hd_le
      have habs_le : |(∫ ξ in Pset S, fScal ξ ∂μ) - ∫ ξ in Pset S, fScal ξ ∂ν| ≤ Dval :=
        (ENNReal.ofReal_le_iff_le_toReal hd_ne_top).mp hd_le
      have hpull : (∫ ξ in Pset S, fScal ξ ∂μ) - ∫ ξ in Pset S, fScal ξ ∂ν =
          Lstar⁻¹ * ((∫ ξ in Pset S, gExt ξ ∂μ) - ∫ ξ in Pset S, gExt ξ ∂ν) := by
        simp only [fScal, integral_const_mul, mul_sub]
      rw [hpull, abs_mul, abs_of_pos (inv_pos.mpr hLstar_pos)] at habs_le
      have hmul := mul_le_mul_of_nonneg_left habs_le (le_of_lt hLstar_pos)
      rwa [mul_inv_cancel_left₀ (ne_of_gt hLstar_pos)] at hmul
    calc |∑ S : Finset (Fin M),
            (((-1 : ℝ) ^ S.card) * (∫ ξ in Pset S, gExt ξ ∂μ) -
             ((-1 : ℝ) ^ S.card) * (∫ ξ in Pset S, gExt ξ ∂ν))|
        ≤ ∑ S : Finset (Fin M),
            |((-1 : ℝ) ^ S.card) * (∫ ξ in Pset S, gExt ξ ∂μ) -
             ((-1 : ℝ) ^ S.card) * (∫ ξ in Pset S, gExt ξ ∂ν)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S : Finset (Fin M), Lstar * Dval := Finset.sum_le_sum fun S _ => hS_bound S
      _ = (2 : ℝ) ^ M * Lstar * Dval := by
          simp [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
          ring
  · rw [Set.not_nonempty_iff_eq_empty] at hAne
    rw [hAne]
    simp only [Measure.restrict_empty, integral_zero_measure, sub_self, abs_zero]
    positivity

private lemma core_bound_on_box {m s r mh mb M D kΞ : ℕ}
    (P : MIProgram m s r mh mb) (hkΞ : P.Ξ ∈ PolyAtMost s kΞ) (hB2 : P.B2)
    (aZ : Fin M → Fin r → ℤ) {L_LP C_H M₁ M₀ M_f ρ : ℝ}
    (hL_LP_pos : 0 < L_LP) (hM₁_nn : 0 ≤ M₁) (hM₀_nn : 0 ≤ M₀) (hMf_pos : 0 < M_f) (hρ : 1 ≤ ρ)
    (hPhi_fin : ∀ t ∈ P.recourse.Tset, P.recourse.Phi t ≠ ⊤ ∧ P.recourse.Phi t ≠ ⊥)
    (hcell_lip : ∀ t ∈ P.recourse.Tset, ∀ t' ∈ P.recourse.Tset,
      (∀ j : Fin M, ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉ =
        ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t' i⌉) →
      |(P.recourse.Phi t).toReal - (P.recourse.Phi t').toReal| ≤ L_LP * ‖t - t'‖)
    (hcell_count : ∀ R : ℝ, 1 ≤ R →
      ∃ S : Finset (Fin M → ℤ),
        (∀ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R,
          (fun j => ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * t i⌉) ∈ S) ∧
        (S.card : ℝ) ≤ (C_H * R) ^ r)
    {x : EuclideanSpace ℝ (Fin m)} (hxX : x ∈ P.X)
    (hg_lip : ∀ ξ₁ ξ₂, ‖(P.h ξ₁ - P.T ξ₁ x) - (P.h ξ₂ - P.T ξ₂ x)‖ ≤ M₁ * ‖ξ₁ - ξ₂‖)
    (hg_norm : ∀ ξ, ‖P.h ξ - P.T ξ x‖ ≤ M₁ * ‖ξ‖ + M₀)
    {μ ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hμ_int_max : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => max (1 : ℝ) ‖ξ‖) μ)
    (hν_int_max : Integrable (fun ξ : EuclideanSpace ℝ (Fin s) => max (1 : ℝ) ‖ξ‖) ν)
    (hd_ne_top : d1phk ((kΞ + (s + s)) + M) μ ν ≠ ⊤)
    (hF_bound : ∀ ξ, ‖P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal) ξ‖ ≤ M_f * max 1 ‖ξ‖)
    (hF_int_μ : Integrable (P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)) μ)
    (hF_int_ν : Integrable (P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)) ν) :
    |(∫ ξ in P.Ξ ∩ {ξ : EuclideanSpace ℝ (Fin s) | ∀ i : Fin s, |ξ i| ≤ ρ},
        P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal) ξ ∂μ) -
      ∫ ξ in P.Ξ ∩ {ξ : EuclideanSpace ℝ (Fin s) | ∀ i : Fin s, |ξ i| ≤ ρ},
        P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal) ξ ∂ν| ≤
      (C_H * (M₁ * Real.sqrt (s : ℝ) + M₀ + 1)) ^ r *
        ((2 : ℝ) ^ M * max (L_LP * M₁) M_f) * ρ ^ r *
        (d1phk ((kΞ + (s + s)) + M) μ ν).toReal := by
  classical
  let F : EuclideanSpace ℝ (Fin s) → ℝ := P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)
  let Qρ : Set (EuclideanSpace ℝ (Fin s)) := {ξ | ∀ i : Fin s, |ξ i| ≤ ρ}
  have hQρ_poly : Qρ ∈ PolyAtMost s (s + s) := box_mem_polyAtMost ρ
  have hΞQ_poly : P.Ξ ∩ Qρ ∈ PolyAtMost s (kΞ + (s + s)) := polyAtMost_inter hkΞ hQρ_poly
  have hΞQ_meas : MeasurableSet (P.Ξ ∩ Qρ) := (polyAtMost_isClosed hΞQ_poly).measurableSet
  let C_g : ℝ := M₁ * Real.sqrt (s : ℝ) + M₀ + 1
  let Lstar : ℝ := max (L_LP * M₁) M_f
  let Dval : ℝ := (d1phk ((kΞ + (s + s)) + M) μ ν).toReal
  have hLstar_pos : 0 < Lstar := lt_of_lt_of_le hMf_pos (le_max_right _ _)
  have hDval_nn : 0 ≤ Dval := ENNReal.toReal_nonneg
  let R : ℝ := C_g * ρ
  have hR_ge1 : 1 ≤ R := by
    have hCg_ge1 : 1 ≤ C_g := by
      dsimp only [C_g]; linarith [mul_nonneg hM₁_nn (Real.sqrt_nonneg (s : ℝ)), hM₀_nn]
    nlinarith
  obtain ⟨S_cells, hS_cover, hS_card⟩ := hcell_count R hR_ge1
  let g_x : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin r) := fun ξ => P.h ξ - P.T ξ x
  have hnorm_Qρ : ∀ ξ ∈ Qρ, ‖ξ‖ ≤ Real.sqrt (s : ℝ) * ρ := by
    intro ξ hξ
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i : Fin s, ‖ξ i‖ ^ 2 ≤ (s : ℝ) * ρ ^ 2 := by
      calc ∑ i : Fin s, ‖ξ i‖ ^ 2
          ≤ ∑ _i : Fin s, ρ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hi : ‖ξ i‖ ≤ ρ := by simpa [Real.norm_eq_abs] using hξ i
            exact pow_le_pow_left₀ (norm_nonneg _) hi 2
        _ = (s : ℝ) * ρ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc Real.sqrt (∑ i : Fin s, ‖ξ i‖ ^ 2)
        ≤ Real.sqrt ((s : ℝ) * ρ ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (s : ℝ) * Real.sqrt (ρ ^ 2) := Real.sqrt_mul (Nat.cast_nonneg s) _
      _ = Real.sqrt (s : ℝ) * ρ := by rw [Real.sqrt_sq (by linarith)]
  have hgx_ball : ∀ ξ ∈ P.Ξ ∩ Qρ, g_x ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) R := by
    intro ξ ⟨_, hξQ⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖g_x ξ‖ ≤ M₁ * ‖ξ‖ + M₀ := hg_norm ξ
      _ ≤ M₁ * (Real.sqrt (s : ℝ) * ρ) + M₀ :=
          add_le_add (mul_le_mul_of_nonneg_left (hnorm_Qρ ξ hξQ) hM₁_nn) le_rfl
      _ ≤ R := by dsimp only [R, C_g]; nlinarith [hM₀_nn]
  let hLin : EuclideanSpace ℝ (Fin s) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    P.h.linear.toContinuousLinearMap
  let TLin : EuclideanSpace ℝ (Fin s) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
    P.T.linear.toContinuousLinearMap
  have hh_apply : ∀ ξ, P.h ξ = hLin ξ + P.h 0 := fun ξ => by
    have h := P.h.map_vadd 0 ξ
    simpa only [vadd_eq_add, add_zero, hLin, LinearMap.coe_toContinuousLinearMap'] using h
  have hT_apply : ∀ ξ, P.T ξ = TLin ξ + P.T 0 := fun ξ => by
    have h := P.T.map_vadd 0 ξ
    simpa only [vadd_eq_add, add_zero, TLin, LinearMap.coe_toContinuousLinearMap'] using h
  let ℓψ : Fin M → (EuclideanSpace ℝ (Fin s) →ₗ[ℝ] ℝ) := fun j =>
    { toFun := fun ξ =>
        (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * ((hLin ξ - (TLin ξ) x) i)
      map_add' := fun u v => by
        have hcoord : ∀ i : Fin r,
            ((hLin (u + v) - (TLin (u + v)) x) i) =
            ((hLin u - (TLin u) x) i) + ((hLin v - (TLin v) x) i) := by
          intro i
          rw [map_add, map_add, _root_.add_apply]
          change (hLin u i + hLin v i) - ((TLin u) x i + (TLin v) x i) =
            (hLin u i - (TLin u) x i) + (hLin v i - (TLin v) x i)
          ring
        simp_rw [hcoord, mul_add, Finset.sum_add_distrib]
        rw [mul_add]
      map_smul' := fun c u => by
        simp only [RingHom.id_apply, smul_eq_mul]
        have hcoord : ∀ i : Fin r,
            ((hLin (c • u) - (TLin (c • u)) x) i) =
            c * ((hLin u - (TLin u) x) i) := by
          intro i
          rw [map_smul, map_smul, _root_.smul_apply]
          change c * hLin u i - c * (TLin u) x i = c * (hLin u i - (TLin u) x i)
          ring
        simp_rw [hcoord]
        calc (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * (c * ((hLin u - (TLin u) x) i))
            = (D : ℝ) * ∑ i : Fin r, c * ((aZ j i : ℝ) * ((hLin u - (TLin u) x) i)) := by
              congr 1; exact Finset.sum_congr rfl fun i _ => by ring
          _ = c * ((D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * ((hLin u - (TLin u) x) i)) := by
              rw [← Finset.mul_sum]; ring }
  let vψ : Fin M → ℝ := fun j =>
    (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * ((P.h 0 - P.T 0 x) i)
  let ψ : Fin M → EuclideanSpace ℝ (Fin s) → ℝ := fun j ξ =>
    (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * (g_x ξ i)
  have hψ_decomp : ∀ j ξ, ψ j ξ = ℓψ j ξ + vψ j := by
    intro j ξ
    change (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * ((P.h ξ - (P.T ξ) x) i) =
      (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * ((hLin ξ - (TLin ξ) x) i) +
      (D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * ((P.h 0 - (P.T 0) x) i)
    have hcoord : ∀ i : Fin r,
        ((P.h ξ - (P.T ξ) x) i) =
        ((hLin ξ - (TLin ξ) x) i) + ((P.h 0 - (P.T 0) x) i) := by
      intro i
      rw [hh_apply ξ, hT_apply ξ, _root_.add_apply]
      change (hLin ξ i + P.h 0 i) - ((TLin ξ) x i + (P.T 0) x i) =
        (hLin ξ i - (TLin ξ) x i) + (P.h 0 i - (P.T 0) x i)
      ring
    simp_rw [hcoord, mul_add, Finset.sum_add_distrib]
    rw [mul_add]
  let A : (Fin M → ℤ) → Set (EuclideanSpace ℝ (Fin s)) := fun κ =>
    {ξ | ξ ∈ P.Ξ ∩ Qρ ∧ ∀ j : Fin M, ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j) ∧
      (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)}
  have hA_meas : ∀ κ, MeasurableSet (A κ) := by
    intro κ
    have hcont : ∀ j, Continuous (fun ξ => ℓψ j ξ + vψ j) := fun j =>
      ((ℓψ j).continuous_of_finiteDimensional).add continuous_const
    have heq : A κ = (P.Ξ ∩ Qρ) ∩ ⋂ j : Fin M,
        ({ξ | ((κ j : ℝ) - 1) < (ℓψ j ξ + vψ j)} ∩ {ξ | (ℓψ j ξ + vψ j) ≤ (κ j : ℝ)}) := by
      ext ξ
      simp only [A, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    refine hΞQ_meas.inter (MeasurableSet.iInter fun j => ?_)
    exact (isOpen_lt continuous_const (hcont j)).measurableSet.inter
      (isClosed_le (hcont j) continuous_const).measurableSet
  have hA_disj : Set.PairwiseDisjoint (S_cells : Set (Fin M → ℤ)) A := by
    intro κ₁ _ κ₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ξ h1 h2
    apply hne
    ext j
    have hc1 : ⌈ℓψ j ξ + vψ j⌉ = κ₁ j := Int.ceil_eq_iff.mpr (h1.2 j)
    have hc2 : ⌈ℓψ j ξ + vψ j⌉ = κ₂ j := Int.ceil_eq_iff.mpr (h2.2 j)
    exact hc1.symm.trans hc2
  have hA_union : (⋃ κ ∈ S_cells, A κ) = P.Ξ ∩ Qρ := by
    ext ξ
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨κ, _, hξA⟩; exact hξA.1
    · intro hξ
      let κ : Fin M → ℤ := fun j => ⌈ψ j ξ⌉
      refine ⟨κ, hS_cover (g_x ξ) (hgx_ball ξ hξ), hξ, fun j => ?_⟩
      rw [← hψ_decomp j ξ]
      exact Int.ceil_eq_iff.mp rfl
  have hcell_est : ∀ κ ∈ S_cells,
      |(∫ ξ in A κ, F ξ ∂μ) - ∫ ξ in A κ, F ξ ∂ν| ≤ (2 : ℝ) ^ M * Lstar * Dval := by
    intro κ _
    have hF_lip_A : ∀ ξ₁ ∈ A κ, ∀ ξ₂ ∈ A κ, |F ξ₁ - F ξ₂| ≤ (L_LP * M₁) * ‖ξ₁ - ξ₂‖ := by
      intro ξ₁ h1 ξ₂ h2
      have hξ₁Ξ : ξ₁ ∈ P.Ξ := h1.1.1
      have hξ₂Ξ : ξ₂ ∈ P.Ξ := h2.1.1
      have ht₁ : g_x ξ₁ ∈ P.recourse.Tset := hB2 ξ₁ hξ₁Ξ x hxX
      have ht₂ : g_x ξ₂ ∈ P.recourse.Tset := hB2 ξ₂ hξ₂Ξ x hxX
      have hft₁ := hPhi_fin (g_x ξ₁) ht₁
      have hft₂ := hPhi_fin (g_x ξ₂) ht₂
      have hF₁ : F ξ₁ = inner ℝ P.c x + (P.recourse.Phi (g_x ξ₁)).toReal := by
        simp only [F, Set.indicator_of_mem hξ₁Ξ]
        change (((inner ℝ P.c x : ℝ) : EReal) + P.recourse.Phi (g_x ξ₁)).toReal = _
        rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hft₁.1 hft₁.2,
          EReal.toReal_coe]
      have hF₂ : F ξ₂ = inner ℝ P.c x + (P.recourse.Phi (g_x ξ₂)).toReal := by
        simp only [F, Set.indicator_of_mem hξ₂Ξ]
        change (((inner ℝ P.c x : ℝ) : EReal) + P.recourse.Phi (g_x ξ₂)).toReal = _
        rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hft₂.1 hft₂.2,
          EReal.toReal_coe]
      have hsame : ∀ j : Fin M,
          ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * (g_x ξ₁) i⌉ =
          ⌈(D : ℝ) * ∑ i : Fin r, (aZ j i : ℝ) * (g_x ξ₂) i⌉ := by
        intro j
        change ⌈ψ j ξ₁⌉ = ⌈ψ j ξ₂⌉
        rw [hψ_decomp j ξ₁, hψ_decomp j ξ₂]
        exact (Int.ceil_eq_iff.mpr (h1.2 j)).trans (Int.ceil_eq_iff.mpr (h2.2 j)).symm
      have hPhi_diff := hcell_lip (g_x ξ₁) ht₁ (g_x ξ₂) ht₂ hsame
      rw [hF₁, hF₂, add_sub_add_left_eq_sub]
      calc |(P.recourse.Phi (g_x ξ₁)).toReal - (P.recourse.Phi (g_x ξ₂)).toReal|
          ≤ L_LP * ‖g_x ξ₁ - g_x ξ₂‖ := hPhi_diff
        _ ≤ L_LP * (M₁ * ‖ξ₁ - ξ₂‖) :=
            mul_le_mul_of_nonneg_left (hg_lip ξ₁ ξ₂) (le_of_lt hL_LP_pos)
        _ = (L_LP * M₁) * ‖ξ₁ - ξ₂‖ := (mul_assoc _ _ _).symm
    have hF_bdd_A : ∀ ζ ∈ A κ, -(M_f * max 1 (Real.sqrt (s : ℝ) * ρ)) ≤ F ζ := by
      intro ζ hζ
      have h1 : |F ζ| ≤ M_f * max 1 ‖ζ‖ := by simpa [Real.norm_eq_abs] using hF_bound ζ
      have h2 : max (1 : ℝ) ‖ζ‖ ≤ max 1 (Real.sqrt (s : ℝ) * ρ) :=
        max_le_max_left 1 (hnorm_Qρ ζ hζ.1.2)
      have h3 : |F ζ| ≤ M_f * max 1 (Real.sqrt (s : ℝ) * ρ) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hMf_pos))
      exact (abs_le.mp h3).1
    exact core_cell_bound hΞQ_poly ℓψ vψ κ F (mul_nonneg (le_of_lt hL_LP_pos) hM₁_nn) hMf_pos
      hμ_int_max hν_int_max hd_ne_top hF_lip_A
      (fun ξ _ => by simpa [Real.norm_eq_abs] using hF_bound ξ) hF_bdd_A
  have hcore_μ : (∫ ξ in P.Ξ ∩ Qρ, F ξ ∂μ) = ∑ κ ∈ S_cells, ∫ ξ in A κ, F ξ ∂μ := by
    rw [← hA_union]
    exact integral_biUnion_finset S_cells (fun κ _ => hA_meas κ) hA_disj
      (fun κ _ => hF_int_μ.integrableOn)
  have hcore_ν : (∫ ξ in P.Ξ ∩ Qρ, F ξ ∂ν) = ∑ κ ∈ S_cells, ∫ ξ in A κ, F ξ ∂ν := by
    rw [← hA_union]
    exact integral_biUnion_finset S_cells (fun κ _ => hA_meas κ) hA_disj
      (fun κ _ => hF_int_ν.integrableOn)
  change |(∫ ξ in P.Ξ ∩ Qρ, F ξ ∂μ) - ∫ ξ in P.Ξ ∩ Qρ, F ξ ∂ν| ≤
    (C_H * C_g) ^ r * ((2 : ℝ) ^ M * Lstar) * ρ ^ r * Dval
  rw [hcore_μ, hcore_ν, ← Finset.sum_sub_distrib]
  calc |∑ κ ∈ S_cells, ((∫ ξ in A κ, F ξ ∂μ) - ∫ ξ in A κ, F ξ ∂ν)|
      ≤ ∑ κ ∈ S_cells, |(∫ ξ in A κ, F ξ ∂μ) - ∫ ξ in A κ, F ξ ∂ν| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _κ ∈ S_cells, (2 : ℝ) ^ M * Lstar * Dval :=
        Finset.sum_le_sum fun κ hκ => hcell_est κ hκ
    _ = (S_cells.card : ℝ) * ((2 : ℝ) ^ M * Lstar * Dval) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C_H * R) ^ r * ((2 : ℝ) ^ M * Lstar * Dval) :=
        mul_le_mul_of_nonneg_right hS_card (by positivity)
    _ = (C_H * C_g) ^ r * ((2 : ℝ) ^ M * Lstar) * ρ ^ r * Dval := by
        dsimp only [R]
        rw [show C_H * (C_g * ρ) = (C_H * C_g) * ρ by ring, mul_pow]
        ring

/-! ### Main proof helper -/

private lemma estimate_12_proof {m s r mh mb : ℕ} (P : MIProgram m s r mh mb)
    (hΞ : IsPolyhedron P.Ξ)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3)
    {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PpK P.Ξ p K)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ ν ∈ PpK P.Ξ p K, d1phk k μ ν < ENNReal.ofReal η₀ →
        dFU P.f0 P.X U μ ν ≤
          ENNReal.ofReal (C * (d1phk k μ ν).toReal ^ (1 / (1 + (r : ℝ) / (p - 1)))) := by
  classical
  -- Unpack Ξ polyhedron representation
  obtain ⟨kΞ, hkΞ⟩ := hΞ
  have hΞ_closed : IsClosed P.Ξ := polyAtMost_isClosed hkΞ
  have hΞ_meas : MeasurableSet P.Ξ := hΞ_closed.measurableSet
  -- Unpack lattice-cell Lipschitzness of Φ
  obtain ⟨M, D, aZ, L_LP, hD_pos, hL_LP_pos, hcell_lip⟩ :=
    phi_lipschitz_on_cell P.recourse hB1 hB3
  -- Unpack cell count bound in balls of ℝ^r
  obtain ⟨C_H, hCH_pos, hcell_count⟩ := cell_count_ball D hD_pos aZ
  -- Unpack finiteness of Φ on Tset and growth bound on f0
  have hPhi_fin := (ProbMetricStab.MixedInt.lemma_3_5_b P.recourse hB1 hB3).1
  obtain ⟨α, β, hα_pos, hβ_pos, _, hgrowth, _⟩ :=
    ProbMetricStab.MixedInt.growth_bound P hB1 hB2 hB3
  -- Bound on closure U
  obtain ⟨R_U, hRU_ball⟩ := (hUb.closure).subset_closedBall (0 : EuclideanSpace ℝ (Fin m))
  let R_U' : ℝ := max 0 R_U
  have hRU'_nn : 0 ≤ R_U' := le_max_left _ _
  have hRU_bound : ∀ x ∈ closure U, ‖x‖ ≤ R_U' := fun x hx =>
    le_trans (by simpa [Metric.mem_closedBall, dist_zero_right] using hRU_ball hx) (le_max_right _ _)
  -- Operator norm bounds for the linear parts of P.h and P.T
  let hLin : EuclideanSpace ℝ (Fin s) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    P.h.linear.toContinuousLinearMap
  let TLin : EuclideanSpace ℝ (Fin s) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
    P.T.linear.toContinuousLinearMap
  let C_h : ℝ := ‖hLin‖
  let C_T : ℝ := ‖TLin‖
  have hCh_nn : 0 ≤ C_h := norm_nonneg hLin
  have hCT_nn : 0 ≤ C_T := norm_nonneg TLin
  have hh_apply : ∀ ξ, P.h ξ = hLin ξ + P.h 0 := fun ξ => by
    have h := P.h.map_vadd 0 ξ
    simpa only [vadd_eq_add, add_zero, hLin, LinearMap.coe_toContinuousLinearMap'] using h
  have hT_apply : ∀ ξ, P.T ξ = TLin ξ + P.T 0 := fun ξ => by
    have h := P.T.map_vadd 0 ξ
    simpa only [vadd_eq_add, add_zero, TLin, LinearMap.coe_toContinuousLinearMap'] using h
  -- Uniform Lipschitz and growth constants for g_x(ξ) = h(ξ) - T(ξ) x and f0(ξ, x)
  let M₁ : ℝ := C_h + C_T * R_U'
  let M₀ : ℝ := ‖P.h 0‖ + ‖P.T 0‖ * R_U'
  have hM₁_nn : 0 ≤ M₁ := by positivity
  have hM₀_nn : 0 ≤ M₀ := by positivity
  have hg_lip : ∀ x ∈ closure U, ∀ ξ₁ ξ₂,
      ‖(P.h ξ₁ - P.T ξ₁ x) - (P.h ξ₂ - P.T ξ₂ x)‖ ≤ M₁ * ‖ξ₁ - ξ₂‖ := by
    intro x hx ξ₁ ξ₂
    have heq : (P.h ξ₁ - P.T ξ₁ x) - (P.h ξ₂ - P.T ξ₂ x) =
        hLin (ξ₁ - ξ₂) - (TLin (ξ₁ - ξ₂)) x := by
      rw [hh_apply ξ₁, hh_apply ξ₂, hT_apply ξ₁, hT_apply ξ₂]
      simp only [_root_.add_apply, map_sub, _root_.sub_apply]
      abel
    rw [heq]
    calc ‖hLin (ξ₁ - ξ₂) - (TLin (ξ₁ - ξ₂)) x‖
        ≤ ‖hLin (ξ₁ - ξ₂)‖ + ‖(TLin (ξ₁ - ξ₂)) x‖ := norm_sub_le _ _
      _ ≤ C_h * ‖ξ₁ - ξ₂‖ + ‖TLin (ξ₁ - ξ₂)‖ * ‖x‖ :=
          add_le_add (hLin.le_opNorm _) ((TLin (ξ₁ - ξ₂)).le_opNorm x)
      _ ≤ C_h * ‖ξ₁ - ξ₂‖ + (C_T * ‖ξ₁ - ξ₂‖) * R_U' := by
          refine add_le_add le_rfl ?_
          exact mul_le_mul (TLin.le_opNorm _) (hRU_bound x hx) (norm_nonneg _) (by positivity)
      _ = M₁ * ‖ξ₁ - ξ₂‖ := by dsimp only [M₁]; ring
  have hg_norm : ∀ x ∈ closure U, ∀ ξ, ‖P.h ξ - P.T ξ x‖ ≤ M₁ * ‖ξ‖ + M₀ := by
    intro x hx ξ
    have h0 : ‖P.h 0 - P.T 0 x‖ ≤ M₀ := by
      calc ‖P.h 0 - P.T 0 x‖
          ≤ ‖P.h 0‖ + ‖P.T 0 x‖ := norm_sub_le _ _
        _ ≤ ‖P.h 0‖ + ‖P.T 0‖ * ‖x‖ := add_le_add le_rfl ((P.T 0).le_opNorm x)
        _ ≤ ‖P.h 0‖ + ‖P.T 0‖ * R_U' :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hRU_bound x hx) (norm_nonneg _))
    have hdiff := hg_lip x hx ξ 0
    simp only [sub_zero] at hdiff
    calc ‖P.h ξ - P.T ξ x‖
        = ‖((P.h ξ - P.T ξ x) - (P.h 0 - P.T 0 x)) + (P.h 0 - P.T 0 x)‖ := by abel_nf
      _ ≤ ‖(P.h ξ - P.T ξ x) - (P.h 0 - P.T 0 x)‖ + ‖P.h 0 - P.T 0 x‖ := norm_add_le _ _
      _ ≤ M₁ * ‖ξ‖ + M₀ := add_le_add hdiff h0
  let M_f : ℝ := ‖P.c‖ * R_U' + α * (M₀ + M₁) + β + 1
  have hMf_pos : 0 < M_f := by positivity
  have hf0_growth : ∀ x ∈ P.X ∩ closure U, ∀ ξ ∈ P.Ξ,
      |(P.f0 ξ x).toReal| ≤ M_f * max 1 ‖ξ‖ := by
    intro x ⟨hxX, hxU⟩ ξ hξ
    have hgb := (hgrowth ξ hξ x hxX).2.2
    have hh_le : ‖P.h ξ‖ ≤ C_h * ‖ξ‖ + ‖P.h 0‖ := by
      rw [hh_apply ξ]
      exact le_trans (norm_add_le _ _) (add_le_add (hLin.le_opNorm ξ) le_rfl)
    have hT_le : ‖P.T ξ‖ ≤ C_T * ‖ξ‖ + ‖P.T 0‖ := by
      rw [hT_apply ξ]
      exact le_trans (norm_add_le _ _) (add_le_add (TLin.le_opNorm ξ) le_rfl)
    have h1 : 1 ≤ max (1 : ℝ) ‖ξ‖ := le_max_left _ _
    have h2 : ‖ξ‖ ≤ max (1 : ℝ) ‖ξ‖ := le_max_right _ _
    have hRU := hRU_bound x hxU
    have hT_mul : ‖P.T ξ‖ * ‖x‖ ≤ (C_T * ‖ξ‖ + ‖P.T 0‖) * R_U' :=
      mul_le_mul hT_le hRU (norm_nonneg _) (by positivity)
    have hc_mul : ‖P.c‖ * ‖x‖ ≤ ‖P.c‖ * R_U' :=
      mul_le_mul_of_nonneg_left hRU (norm_nonneg _)
    have hsum : ‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖ ≤ M₀ + M₁ * ‖ξ‖ := by
      dsimp only [M₀, M₁]; linarith
    have hsum2 : M₀ + M₁ * ‖ξ‖ ≤ (M₀ + M₁) * max 1 ‖ξ‖ := by
      calc M₀ + M₁ * ‖ξ‖
          ≤ M₀ * max 1 ‖ξ‖ + M₁ * max 1 ‖ξ‖ :=
            add_le_add (le_mul_of_one_le_right hM₀_nn h1) (mul_le_mul_of_nonneg_left h2 hM₁_nn)
        _ = (M₀ + M₁) * max 1 ‖ξ‖ := by ring
    have hcb_nn : 0 ≤ ‖P.c‖ * R_U' + β := by positivity
    have hcb_le : ‖P.c‖ * R_U' + β ≤ (‖P.c‖ * R_U' + β + 1) * max 1 ‖ξ‖ := by
      calc ‖P.c‖ * R_U' + β ≤ ‖P.c‖ * R_U' + β + 1 := by linarith
        _ ≤ (‖P.c‖ * R_U' + β + 1) * max 1 ‖ξ‖ := le_mul_of_one_le_right (by linarith) h1
    calc |(P.f0 ξ x).toReal|
        ≤ ‖P.c‖ * ‖x‖ + α * (‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖) + β := hgb
      _ ≤ ‖P.c‖ * R_U' + α * ((M₀ + M₁) * max 1 ‖ξ‖) + β := by
          have ha : α * (‖P.h ξ‖ + ‖P.T ξ‖ * ‖x‖) ≤ α * ((M₀ + M₁) * max 1 ‖ξ‖) :=
            mul_le_mul_of_nonneg_left (le_trans hsum hsum2) (le_of_lt hα_pos)
          linarith
      _ = (‖P.c‖ * R_U' + β) + α * (M₀ + M₁) * max 1 ‖ξ‖ := by ring
      _ ≤ (‖P.c‖ * R_U' + β + 1) * max 1 ‖ξ‖ + α * (M₀ + M₁) * max 1 ‖ξ‖ :=
          add_le_add hcb_le le_rfl
      _ = M_f * max 1 ‖ξ‖ := by dsimp only [M_f]; ring
  -- Define final constants
  let Lstar : ℝ := max (L_LP * M₁) M_f
  have hLstar_pos : 0 < Lstar := lt_of_lt_of_le hMf_pos (le_max_right _ _)
  let C_g : ℝ := M₁ * Real.sqrt (s : ℝ) + M₀ + 1
  have hCg_pos : 0 < C_g := by positivity
  let C_A : ℝ := (C_H * C_g) ^ r * ((2 : ℝ) ^ M * Lstar)
  let C_B : ℝ := 2 * M_f * K
  have hCA_pos : 0 < C_A := by positivity
  have hCB_pos : 0 < C_B := by positivity
  let C : ℝ := C_A + C_B
  have hC_pos : 0 < C := by positivity
  let k : ℕ := (kΞ + (s + s)) + M
  refine ⟨C, hC_pos, k, 1, zero_lt_one, fun ν hν hdlt => ?_⟩
  -- Moments of μ and ν
  obtain ⟨hμ_int_p, hμ_le_K, hμ_int_max⟩ := rpow_p_integrable_of_PpK hp hK hμ
  obtain ⟨hν_int_p, hν_le_K, hν_int_max⟩ := rpow_p_integrable_of_PpK hp hK hν
  have hd_ne_top : d1phk k μ ν ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hdlt (le_of_lt ENNReal.ofReal_lt_top))
  let Dval : ℝ := (d1phk k μ ν).toReal
  have hDval_nn : 0 ≤ Dval := ENNReal.toReal_nonneg
  have hDval_lt1 : Dval < 1 := by
    have h1 : ENNReal.ofReal 1 = 1 := ENNReal.ofReal_one
    rw [h1] at hdlt
    have := (ENNReal.toReal_lt_toReal hd_ne_top ENNReal.one_ne_top).mpr hdlt
    simpa [Dval] using this
  -- Establish bound for each x ∈ P.X ∩ closure U
  unfold dFU
  refine iSup₂_le fun x hx => ?_
  have hxX : x ∈ P.X := hx.1
  have hxU : x ∈ closure U := hx.2
  let F : EuclideanSpace ℝ (Fin s) → ℝ := P.Ξ.indicator (fun ξ => (P.f0 ξ x).toReal)
  have hF_meas : Measurable F := measurable_indicator_f0 P hΞ_closed hB1 hB2 hB3 hxX
  have hF_bound : ∀ ξ, ‖F ξ‖ ≤ M_f * max 1 ‖ξ‖ := by
    intro ξ
    by_cases hξ : ξ ∈ P.Ξ
    · simp only [F, Set.indicator_of_mem hξ, Real.norm_eq_abs]
      exact hf0_growth x hx ξ hξ
    · simp only [F, Set.indicator_of_notMem hξ, norm_zero]
      exact mul_nonneg (le_of_lt hMf_pos) (le_trans zero_le_one (le_max_left _ _))
  have hF_int_μ : Integrable F μ :=
    (hμ_int_max.const_mul M_f).mono' hF_meas.aestronglyMeasurable (Filter.Eventually.of_forall hF_bound)
  have hF_int_ν : Integrable F ν :=
    (hν_int_max.const_mul M_f).mono' hF_meas.aestronglyMeasurable (Filter.Eventually.of_forall hF_bound)
  have hf0_ae_μ : ∀ᵐ ξ ∂μ, P.f0 ξ x = (F ξ : EReal) := by
    have hmem : ∀ᵐ ξ ∂μ, ξ ∈ P.Ξ := by
      rw [ae_iff]; exact hμ.1.1.2
    filter_upwards [hmem] with ξ hξ
    have hfin := hgrowth ξ hξ x hxX
    simp only [F, Set.indicator_of_mem hξ]
    exact (EReal.coe_toReal hfin.1 hfin.2.1).symm
  have hf0_ae_ν : ∀ᵐ ξ ∂ν, P.f0 ξ x = (F ξ : EReal) := by
    have hmem : ∀ᵐ ξ ∂ν, ξ ∈ P.Ξ := by
      rw [ae_iff]; exact hν.1.1.2
    filter_upwards [hmem] with ξ hξ
    have hfin := hgrowth ξ hξ x hxX
    simp only [F, Set.indicator_of_mem hξ]
    exact (EReal.coe_toReal hfin.1 hfin.2.1).symm
  have hintObj_μ : intObj P.f0 μ x = ((∫ ξ, F ξ ∂μ : ℝ) : EReal) :=
    expect_eq_coe_integral μ (fun ξ => P.f0 ξ x) F hF_int_μ hf0_ae_μ
  have hintObj_ν : intObj P.f0 ν x = ((∫ ξ, F ξ ∂ν : ℝ) : EReal) :=
    expect_eq_coe_integral ν (fun ξ => P.f0 ξ x) F hF_int_ν hf0_ae_ν
  rw [hintObj_μ, hintObj_ν, ← EReal.coe_sub, EReal.abs_def]
  apply ENNReal.ofReal_le_ofReal
  -- Key ρ-parametrized core + tail estimate for every ρ ≥ 1
  have hrho_bound : ∀ ρ : ℝ, 1 ≤ ρ →
      |(∫ ξ, F ξ ∂μ) - ∫ ξ, F ξ ∂ν| ≤ C_A * ρ ^ r * Dval + C_B * ρ ^ (-(p - 1)) := by
    intro ρ hρ
    let Qρ : Set (EuclideanSpace ℝ (Fin s)) := {ξ | ∀ i : Fin s, |ξ i| ≤ ρ}
    have hQρ_poly : Qρ ∈ PolyAtMost s (s + s) := box_mem_polyAtMost ρ
    have hQρ_meas : MeasurableSet Qρ := (polyAtMost_isClosed hQρ_poly).measurableSet
    have hΞQ_meas : MeasurableSet (P.Ξ ∩ Qρ) := hΞ_meas.inter hQρ_meas
    -- Split integral into P.Ξ ∩ Qρ and (P.Ξ ∩ Qρ)ᶜ
    have hsplit_μ : ∫ ξ, F ξ ∂μ = (∫ ξ in P.Ξ ∩ Qρ, F ξ ∂μ) + ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂μ :=
      (integral_add_compl hΞQ_meas hF_int_μ).symm
    have hsplit_ν : ∫ ξ, F ξ ∂ν = (∫ ξ in P.Ξ ∩ Qρ, F ξ ∂ν) + ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂ν :=
      (integral_add_compl hΞQ_meas hF_int_ν).symm
    -- Tail bound on (P.Ξ ∩ Qρ)ᶜ
    have hF_zero : ∀ ξ ∉ P.Ξ, F ξ = 0 := fun ξ hξ => Set.indicator_of_notMem hξ _
    have htail : |(∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂μ) - ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂ν| ≤
        C_B * ρ ^ (-(p - 1)) := by
      have h1 := tail_bound_one hΞ_meas hp hMf_pos hρ hF_zero hF_bound hF_int_μ hμ_int_p hμ_le_K
      have h2 := tail_bound_one hΞ_meas hp hMf_pos hρ hF_zero hF_bound hF_int_ν hν_int_p hν_le_K
      have htri : |(∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂μ) - ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂ν| ≤
          |∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂μ| + |∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂ν| := abs_sub _ _
      dsimp only [C_B]
      linarith
    -- Core bound on P.Ξ ∩ Qρ
    have hcore : |(∫ ξ in P.Ξ ∩ Qρ, F ξ ∂μ) - ∫ ξ in P.Ξ ∩ Qρ, F ξ ∂ν| ≤
        C_A * ρ ^ r * Dval :=
      core_bound_on_box P hkΞ hB2 aZ hL_LP_pos hM₁_nn hM₀_nn hMf_pos hρ hPhi_fin hcell_lip
        hcell_count hxX (hg_lip x hxU) (hg_norm x hxU) hμ_int_max hν_int_max hd_ne_top
        hF_bound hF_int_μ hF_int_ν
    -- Combine core + tail
    rw [hsplit_μ, hsplit_ν]
    have hrearr : ((∫ ξ in P.Ξ ∩ Qρ, F ξ ∂μ) + ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂μ) -
        ((∫ ξ in P.Ξ ∩ Qρ, F ξ ∂ν) + ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂ν) =
        ((∫ ξ in P.Ξ ∩ Qρ, F ξ ∂μ) - ∫ ξ in P.Ξ ∩ Qρ, F ξ ∂ν) +
        ((∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂μ) - ∫ ξ in (P.Ξ ∩ Qρ)ᶜ, F ξ ∂ν) := by ring
    rw [hrearr]
    exact le_trans (abs_add_le _ _) (add_le_add hcore htail)
  -- Optimize ρ ≥ 1
  exact optimize_rho_bound hp hCA_pos hCB_pos hDval_nn hDval_lt1 (abs_nonneg _) hrho_bound

end Helpers

theorem solution {m s r mh mb : ℕ} (P : ProbMetricStab.MixedInt.MIProgram m s r mh mb)
    (hX : IsClosed P.X) (hΞ : ProbMetricStab.MixedInt.IsPolyhedron P.Ξ)
    (hB1 : P.recourse.B1) (hB2 : P.B2) (hB3 : P.recourse.B3)
    {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ ProbMetricStab.MixedInt.PpK P.Ξ p K)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ ν ∈ ProbMetricStab.MixedInt.PpK P.Ξ p K,
        ProbMetricStab.MixedInt.d1phk k μ ν < ENNReal.ofReal η₀ →
          ProbMetricStab.MixedInt.dFU P.f0 P.X U μ ν ≤
            ENNReal.ofReal (C * (ProbMetricStab.MixedInt.d1phk k μ ν).toReal ^
              (1 / (1 + (r : ℝ) / (p - 1)))) :=
  estimate_12_proof P hΞ hB1 hB2 hB3 hp hK μ hμ U hUb
