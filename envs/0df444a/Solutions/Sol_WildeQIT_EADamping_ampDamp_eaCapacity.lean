-- Prove2me | solution 1 for WildeQIT.EADamping.ampDamp_eaCapacity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:26:46.259418+00:00
-- url     : https://prove2.me/submissions/a88f4dcd-a4bd-48bc-be15-ad371b55b433

import Mathlib
import Definitions.Def_WildeQIT_EADamping_ampDamp
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_WildeQIT_Degradable_PureInput
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
import Theorems.Thm_WildeQIT_EADamping_isAchievableEARate_le_channelMutualInfo
import Theorems.Thm_WildeQIT_EADamping_pureInput_mutualInfo_isAchievableEARate

set_option autoImplicit false

namespace WildeQIT.EADamping.Aux7e1785ee
open Matrix

/-- a real sum over eigenvalues in `{0, a, b}` with the first two power sums of `{a, b}` -/
lemma sum_three {ι : Type*} [Fintype ι] (lam : ι → ℝ) (a b : ℝ) (f : ℝ → ℝ) (hf : f 0 = 0)
    (hl : ∀ i, lam i = 0 ∨ lam i = a ∨ lam i = b)
    (h1 : ∑ i, lam i = a + b) (h2 : ∑ i, lam i * lam i = a * a + b * b) :
    ∑ i, f (lam i) = f a + f b := by
  obtain ⟨α, β, hfa, hfb⟩ : ∃ α β : ℝ, α * a + β * (a * a) = f a ∧ α * b + β * (b * b) = f b := by
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb; exact ⟨0, 0, by simp [hf], by simp [hf]⟩
      · refine ⟨0, f b / (b * b), by simp [hf], ?_⟩
        field_simp; ring
    · by_cases hb : b = 0
      · subst hb
        refine ⟨0, f a / (a * a), ?_, by simp [hf]⟩
        field_simp; ring
      · by_cases hab : a = b
        · subst hab
          exact ⟨f a / a, 0, by field_simp; ring, by field_simp; ring⟩
        · have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
          refine ⟨f a / a - (f a / a - f b / b) / (a - b) * a, (f a / a - f b / b) / (a - b),
            ?_, ?_⟩
          · field_simp; ring
          · field_simp; ring
  have hpt : ∀ i, f (lam i) = α * lam i + β * (lam i * lam i) := by
    intro i
    rcases hl i with h | h | h <;> rw [h]
    · simp [hf]
    · exact hfa.symm
    · exact hfb.symm
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, h1, h2]
  linear_combination hfa + hfb

lemma trace_cfc_herm {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  first
    | rw [Unitary.coe_star_mul_self]
    | rw [Unitary.star_mul_self]
    | rw [Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2]
  rw [Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma entropy_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    QAlgorithms.vnEntropy s = ∑ i, -(hs.eigenvalues i * Real.logb 2 (hs.eigenvalues i)) := by
  rw [QAlgorithms.vnEntropy, trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [Finset.sum_neg_distrib]

lemma purity_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    (s * s).trace.re = ∑ i, hs.eigenvalues i * hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x * x) s = s * s := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) s, cfc_id' ℝ s hsa]
  rw [← h1, trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

lemma star_dot_swap {n : Type*} [Fintype n] (v w : n → ℂ) (h : star v ⬝ᵥ w = 0) :
    star w ⬝ᵥ v = 0 := by
  have h' := congrArg star h
  rw [star_zero] at h'
  rw [← h']
  simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- entropy of a sum of two orthogonal rank-one positive operators -/
lemma vn_two {n : Type*} [Fintype n] [DecidableEq n] (v w : n → ℂ) (a b : ℝ)
    (hvw : star v ⬝ᵥ w = 0) (ha : star v ⬝ᵥ v = (a : ℂ)) (hb : star w ⬝ᵥ w = (b : ℂ)) :
    QAlgorithms.vnEntropy (vecMulVec v (star v) + vecMulVec w (star w)) =
      -(a * Real.logb 2 a) - b * Real.logb 2 b := by
  have hwv : star w ⬝ᵥ v = 0 := star_dot_swap v w hvw
  set M := vecMulVec v (star v) + vecMulVec w (star w) with hMdef
  have hM : M.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hMdef, conjTranspose_add, conjTranspose_vecMulVec, conjTranspose_vecMulVec, star_star,
      star_star]
  have hMv : ∀ u : n → ℂ, M *ᵥ u = (star v ⬝ᵥ u) • v + (star w ⬝ᵥ u) • w := by
    intro u
    rw [hMdef, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
  have heig : ∀ j, hM.eigenvalues j = 0 ∨ hM.eigenvalues j = a ∨ hM.eigenvalues j = b := by
    intro j
    have h1 := hM.mulVec_eigenvectorBasis j
    set u : n → ℂ := ⇑(hM.eigenvectorBasis j) with hu
    set μ : ℝ := hM.eigenvalues j with hμ
    have hu0 : u ≠ 0 := by
      intro h
      apply (hM.eigenvectorBasis.orthonormal.ne_zero j)
      ext i
      simpa [hu] using congrFun h i
    have h1' : M *ᵥ u = (μ : ℂ) • u := by
      rw [h1, RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
    have ev : (a : ℂ) * (star v ⬝ᵥ u) = (μ : ℂ) * (star v ⬝ᵥ u) := by
      have e := congrArg (fun x => star v ⬝ᵥ x) h1'
      simp only [hMv, dotProduct_add, dotProduct_smul, ha, hvw, smul_eq_mul, mul_zero,
        add_zero] at e
      linear_combination e
    have ew : (b : ℂ) * (star w ⬝ᵥ u) = (μ : ℂ) * (star w ⬝ᵥ u) := by
      have e := congrArg (fun x => star w ⬝ᵥ x) h1'
      simp only [hMv, dotProduct_add, dotProduct_smul, hb, hwv, smul_eq_mul, mul_zero,
        zero_add] at e
      linear_combination e
    by_contra hne
    push_neg at hne
    obtain ⟨h0, hA, hB⟩ := hne
    have hα : star v ⬝ᵥ u = 0 := by
      have : ((a : ℂ) - μ) * (star v ⬝ᵥ u) = 0 := by linear_combination ev
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast (sub_eq_zero.mp h).symm) hA
      · exact h
    have hβ : star w ⬝ᵥ u = 0 := by
      have : ((b : ℂ) - μ) * (star w ⬝ᵥ u) = 0 := by linear_combination ew
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast (sub_eq_zero.mp h).symm) hB
      · exact h
    have hz : (μ : ℂ) • u = 0 := by rw [← h1', hMv, hα, hβ, zero_smul, zero_smul, add_zero]
    rcases smul_eq_zero.mp hz with h | h
    · exact h0 (by exact_mod_cast h)
    · exact hu0 h
  have htr : ∑ i, hM.eigenvalues i = a + b := by
    have h := hM.trace_eq_sum_eigenvalues
    have h2 : M.trace = (a : ℂ) + b := by
      rw [hMdef, trace_add, trace_vecMulVec, trace_vecMulVec, dotProduct_comm v,
        dotProduct_comm w, ha, hb]
    have h3 : ((∑ i, hM.eigenvalues i : ℝ) : ℂ) = ((a + b : ℝ) : ℂ) := by
      push_cast; exact h.symm.trans h2
    exact_mod_cast h3
  have hsq : ∑ i, hM.eigenvalues i * hM.eigenvalues i = a * a + b * b := by
    rw [← purity_eig hM]
    have h2 : M * M = vecMulVec v (((a : ℂ)) • star v) + vecMulVec w (((b : ℂ)) • star w) := by
      rw [hMdef, add_mul, mul_add, mul_add, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec,
        vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, ha, hb, hvw, hwv, zero_smul, zero_smul,
        vecMulVec_zero, vecMulVec_zero, add_zero, zero_add]
    rw [h2, trace_add, trace_vecMulVec, trace_vecMulVec, dotProduct_smul, dotProduct_smul,
      dotProduct_comm v, dotProduct_comm w, ha, hb]
    simp
  rw [entropy_eig hM]
  exact sum_three _ a b (fun x => -(x * Real.logb 2 x)) (by simp) heig htr hsq

lemma conj_rank_one {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (u : n → ℂ) :
    A * vecMulVec u (star u) * Aᴴ = vecMulVec (A *ᵥ u) (star (A *ᵥ u)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

lemma dot_real {n : Type*} [Fintype n] (f : n → ℝ) :
    star (fun i => ((f i : ℝ) : ℂ)) ⬝ᵥ (fun i => ((f i : ℝ) : ℂ)) = ((∑ i, f i * f i : ℝ) : ℂ) := by
  simp [dotProduct, Pi.star_apply, Complex.conj_ofReal]

lemma dot_real2 {n : Type*} [Fintype n] (f g : n → ℝ) :
    star (fun i => ((f i : ℝ) : ℂ)) ⬝ᵥ (fun i => ((g i : ℝ) : ℂ)) = ((∑ i, f i * g i : ℝ) : ℂ) := by
  simp [dotProduct, Pi.star_apply, Complex.conj_ofReal]

open WildeQIT WildeQIT.EADamping in
/-- the explicit input `√(1-p)|00⟩ + √p|11⟩` -/
noncomputable def uIn (p : ℝ) : Fin 2 × Fin 2 → ℂ := fun x =>
  ((if x = (0, 0) then Real.sqrt (1 - p) else if x = (1, 1) then Real.sqrt p else 0 : ℝ) : ℂ)

lemma uIn_norm (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : ‖(WithLp.toLp 2 (uIn p) : EuclideanSpace ℂ (Fin 2 × Fin 2))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h1 : Real.sqrt (1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith [hp.2])
  have h2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.1
  simp [uIn, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.norm_real, h1, h2]

open WildeQIT WildeQIT.EADamping in
lemma ad_out (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (p : ℝ) :
    idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity
      (WithLp.toLp 2 (uIn p) : EuclideanSpace ℂ (Fin 2 × Fin 2))) =
    vecMulVec (fun x : Fin 2 × Fin 2 => ((if x = (0, 0) then Real.sqrt (1 - p) else
        if x = (1, 1) then Real.sqrt p * Real.sqrt (1 - γ) else 0 : ℝ) : ℂ))
      (star (fun x : Fin 2 × Fin 2 => ((if x = (0, 0) then Real.sqrt (1 - p) else
        if x = (1, 1) then Real.sqrt p * Real.sqrt (1 - γ) else 0 : ℝ) : ℂ))) +
    vecMulVec (fun x : Fin 2 × Fin 2 => ((if x = (1, 0) then Real.sqrt p * Real.sqrt γ else 0 : ℝ) : ℂ))
      (star (fun x : Fin 2 × Fin 2 => ((if x = (1, 0) then Real.sqrt p * Real.sqrt γ else 0 : ℝ) : ℂ))) := by
  have hpd : QAlgorithms.pureDensity
      (WithLp.toLp 2 (uIn p) : EuclideanSpace ℂ (Fin 2 × Fin 2)) = vecMulVec (uIn p) (star (uIn p)) := by
    ext i j
    simp [QAlgorithms.pureDensity, vecMulVec_apply]
  have h01 : ∀ y : Fin 2, y = 0 ∨ y = 1 := by decide
  rw [hpd, idTensorApply, Fintype.sum_eq_add (show (ampDamp γ hγ).ι from (0 : Fin 2))
    (show (ampDamp γ hγ).ι from (1 : Fin 2)) (by exact (by decide : (0 : Fin 2) ≠ 1))
    (fun x hx => by rcases h01 x with h | h <;> [exact absurd h hx.1; exact absurd h hx.2])]
  simp only [ampDamp]
  rw [conj_rank_one, conj_rank_one]
  congr 2 <;> try congr 1
  all_goals
    funext x
    rcases x with ⟨r, b⟩
    fin_cases r <;> fin_cases b <;>
      simp [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply, uIn,
        Complex.conj_ofReal] <;> ring

lemma vn_two_real {n : Type*} [Fintype n] [DecidableEq n] (f g : n → ℝ) (a b : ℝ)
    (hfg : ∑ i, f i * g i = 0) (ha : ∑ i, f i * f i = a) (hb : ∑ i, g i * g i = b) :
    QAlgorithms.vnEntropy (vecMulVec (fun i => ((f i : ℝ) : ℂ)) (star (fun i => ((f i : ℝ) : ℂ))) +
      vecMulVec (fun i => ((g i : ℝ) : ℂ)) (star (fun i => ((g i : ℝ) : ℂ)))) =
      -(a * Real.logb 2 a) - b * Real.logb 2 b := by
  refine vn_two _ _ a b ?_ ?_ ?_
  · rw [dot_real2, hfg]; simp
  · rw [dot_real, ha]
  · rw [dot_real, hb]

open WildeQIT WildeQIT.EADamping in
theorem c1_diag (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∃ φ : WildeQIT.Degradable.PureInput (Fin 2),
      DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)) =
        binaryEntropy p + binaryEntropy ((1 - γ) * p) - binaryEntropy (γ * p) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hγ0 : 0 ≤ γ := hγ.1
  have hγ1 : γ ≤ 1 := hγ.2
  set s := Real.sqrt (1 - p) with hs_def
  set t := Real.sqrt p with ht_def
  set g := Real.sqrt γ with hg_def
  set h := Real.sqrt (1 - γ) with hh_def
  set q := Real.sqrt (1 - (1 - γ) * p) with hq_def
  have hs : s * s = 1 - p := Real.mul_self_sqrt (by linarith)
  have ht : t * t = p := Real.mul_self_sqrt hp0
  have hg : g * g = γ := Real.mul_self_sqrt hγ0
  have hh : h * h = 1 - γ := Real.mul_self_sqrt (by linarith)
  have hq : q * q = 1 - (1 - γ) * p := Real.mul_self_sqrt (by nlinarith)
  have hS : (s : ℂ) * s = 1 - p := by exact_mod_cast hs
  have hT : (t : ℂ) * t = p := by exact_mod_cast ht
  have hG : (g : ℂ) * g = γ := by exact_mod_cast hg
  have hH : (h : ℂ) * h = 1 - γ := by exact_mod_cast hh
  have hQ : (q : ℂ) * q = 1 - (1 - γ) * p := by exact_mod_cast hq
  refine ⟨⟨2, WithLp.toLp 2 (uIn p), uIn_norm p ⟨hp0, hp1⟩⟩, ?_⟩
  show DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ)
    (QAlgorithms.pureDensity (WithLp.toLp 2 (uIn p) : EuclideanSpace ℂ (Fin 2 × Fin 2)))) = _
  rw [ad_out]
  have mR : QAlgorithms.traceRight
      (vecMulVec (fun x : Fin 2 × Fin 2 => ((if x = (0, 0) then s else
          if x = (1, 1) then t * h else 0 : ℝ) : ℂ))
        (star (fun x : Fin 2 × Fin 2 => ((if x = (0, 0) then s else
          if x = (1, 1) then t * h else 0 : ℝ) : ℂ))) +
      vecMulVec (fun x : Fin 2 × Fin 2 => ((if x = (1, 0) then t * g else 0 : ℝ) : ℂ))
        (star (fun x : Fin 2 × Fin 2 => ((if x = (1, 0) then t * g else 0 : ℝ) : ℂ)))) =
      vecMulVec (fun i : Fin 2 => ((if i = 0 then s else 0 : ℝ) : ℂ))
        (star (fun i : Fin 2 => ((if i = 0 then s else 0 : ℝ) : ℂ))) +
      vecMulVec (fun i : Fin 2 => ((if i = 1 then t else 0 : ℝ) : ℂ))
        (star (fun i : Fin 2 => ((if i = 1 then t else 0 : ℝ) : ℂ))) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QAlgorithms.traceRight, vecMulVec_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
      linear_combination ((t : ℂ) * t) * hH + ((t : ℂ) * t) * hG
  have mL : QAlgorithms.traceLeft
      (vecMulVec (fun x : Fin 2 × Fin 2 => ((if x = (0, 0) then s else
          if x = (1, 1) then t * h else 0 : ℝ) : ℂ))
        (star (fun x : Fin 2 × Fin 2 => ((if x = (0, 0) then s else
          if x = (1, 1) then t * h else 0 : ℝ) : ℂ))) +
      vecMulVec (fun x : Fin 2 × Fin 2 => ((if x = (1, 0) then t * g else 0 : ℝ) : ℂ))
        (star (fun x : Fin 2 × Fin 2 => ((if x = (1, 0) then t * g else 0 : ℝ) : ℂ)))) =
      vecMulVec (fun i : Fin 2 => ((if i = 0 then q else 0 : ℝ) : ℂ))
        (star (fun i : Fin 2 => ((if i = 0 then q else 0 : ℝ) : ℂ))) +
      vecMulVec (fun i : Fin 2 => ((if i = 1 then t * h else 0 : ℝ) : ℂ))
        (star (fun i : Fin 2 => ((if i = 1 then t * h else 0 : ℝ) : ℂ))) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QAlgorithms.traceLeft, vecMulVec_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
      linear_combination hS + ((t : ℂ) * t) * hG + (γ : ℂ) * hT - hQ
  rw [DattaDiscord.mutualInfo, mR, mL,
    vn_two_real (fun i : Fin 2 => if i = 0 then s else 0) (fun i : Fin 2 => if i = 1 then t else 0)
      (1 - p) p (by simp [Fin.sum_univ_two]) (by simp [Fin.sum_univ_two, hs])
      (by simp [Fin.sum_univ_two, ht]),
    vn_two_real (fun i : Fin 2 => if i = 0 then q else 0)
      (fun i : Fin 2 => if i = 1 then t * h else 0)
      (1 - (1 - γ) * p) ((1 - γ) * p) (by simp [Fin.sum_univ_two]) (by simp [Fin.sum_univ_two, hq])
      (by simp [Fin.sum_univ_two]; rw [← hh, ← ht]; ring),
    vn_two_real (fun x : Fin 2 × Fin 2 => if x = (0, 0) then s else if x = (1, 1) then t * h else 0)
      (fun x : Fin 2 × Fin 2 => if x = (1, 0) then t * g else 0)
      (1 - γ * p) (γ * p) (by simp [Fintype.sum_prod_type, Fin.sum_univ_two])
      (by simp [Fintype.sum_prod_type, Fin.sum_univ_two]; nlinarith [hs, ht, hh])
      (by simp [Fintype.sum_prod_type, Fin.sum_univ_two]; rw [← hg, ← ht]; ring)]
  simp only [binaryEntropy]
  ring_nf

lemma trace_eig {n : Type*} [Fintype n] [DecidableEq n] {s : Matrix n n ℂ} (hs : s.IsHermitian) :
    s.trace.re = ∑ i, hs.eigenvalues i := by
  have hsa : IsSelfAdjoint s := hs
  have h1 : cfc (fun x : ℝ => x) s = s := cfc_id' ℝ s hsa
  conv_lhs => rw [← h1]
  rw [trace_cfc_herm hs, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- entropy of a trace-one Hermitian matrix whose nonzero eigenvalues solve `x² - x + d = 0` -/
lemma ent_of_quad {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (d : ℝ) (hq : ∀ j, hM.eigenvalues j = 0 ∨ hM.eigenvalues j ^ 2 - hM.eigenvalues j + d = 0)
    (h1 : M.trace = 1) (h2 : (M * M).trace = ((1 - 2 * d : ℝ) : ℂ)) :
    QAlgorithms.vnEntropy M = Real.binEntropy ((1 - √(1 - 4 * d)) / 2) / Real.log 2 := by
  have hsum : ∑ j, hM.eigenvalues j = 1 := by
    rw [← trace_eig hM, h1, Complex.one_re]
  have hd : d ≤ 1 / 4 := by
    by_contra hc
    push_neg at hc
    have h0 : ∀ j, hM.eigenvalues j = 0 := by
      intro j
      rcases hq j with h | h
      · exact h
      · nlinarith [sq_nonneg (hM.eigenvalues j - 1 / 2)]
    simp [h0] at hsum
  set s := √(1 - 4 * d) with hs_def
  have hs : s * s = 1 - 4 * d := Real.mul_self_sqrt (by linarith)
  have hl : ∀ j, hM.eigenvalues j = 0 ∨ hM.eigenvalues j = (1 - s) / 2 ∨
      hM.eigenvalues j = (1 + s) / 2 := by
    intro j
    rcases hq j with h | h
    · exact Or.inl h
    · right
      have hm : (hM.eigenvalues j - (1 - s) / 2) * (hM.eigenvalues j - (1 + s) / 2) = 0 := by
        linear_combination h - (1 / 4) * hs
      rcases mul_eq_zero.mp hm with h' | h'
      · left; linarith
      · right; linarith
  have hsq : ∑ j, hM.eigenvalues j * hM.eigenvalues j =
      (1 - s) / 2 * ((1 - s) / 2) + (1 + s) / 2 * ((1 + s) / 2) := by
    rw [← purity_eig hM, h2, Complex.ofReal_re]
    linear_combination (-1 / 2) * hs
  rw [entropy_eig hM, show (∑ i, -(hM.eigenvalues i * Real.logb 2 (hM.eigenvalues i))) = _ from
    sum_three _ ((1 - s) / 2) ((1 + s) / 2) (fun x => -(x * Real.logb 2 x)) (by simp) hl
      (by rw [hsum]; ring) hsq]
  have hb : (1 + s) / 2 = 1 - (1 - s) / 2 := by ring
  rw [hb]
  simp only [Real.binEntropy, Real.logb, Real.log_inv]
  ring

lemma quad_two (lam A B C C' α β : ℂ) (e1 : lam * α = A * α + C * β)
    (e2 : lam * β = C' * α + B * β) :
    ((lam - A) * (lam - B) - C * C') * α = 0 ∧ ((lam - A) * (lam - B) - C * C') * β = 0 := by
  constructor
  · linear_combination (lam - B) * e1 + C * e2
  · linear_combination C' * e1 + (lam - A) * e2

lemma herm_two {n : Type*} [Fintype n] (v w : n → ℂ) :
    (vecMulVec v (star v) + vecMulVec w (star w)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_add, conjTranspose_vecMulVec, conjTranspose_vecMulVec, star_star, star_star]

/-- entropy of `vv* + ww*` with trace one, via the 2x2 Gram determinant `d` -/
lemma two_vec {n : Type*} [Fintype n] [DecidableEq n] (v w : n → ℂ) (d : ℝ)
    (hs : star v ⬝ᵥ v + star w ⬝ᵥ w = 1)
    (hdet : (star v ⬝ᵥ v) * (star w ⬝ᵥ w) - (star v ⬝ᵥ w) * (star w ⬝ᵥ v) = (d : ℂ)) :
    QAlgorithms.vnEntropy (vecMulVec v (star v) + vecMulVec w (star w)) =
      Real.binEntropy ((1 - √(1 - 4 * d)) / 2) / Real.log 2 := by
  set M := vecMulVec v (star v) + vecMulVec w (star w) with hMdef
  have hM : M.IsHermitian := herm_two v w
  have hMv : ∀ u : n → ℂ, M *ᵥ u = (star v ⬝ᵥ u) • v + (star w ⬝ᵥ u) • w := by
    intro u
    rw [hMdef, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
  have htr : ∀ x y : n → ℂ, (vecMulVec x (star y)).trace = star y ⬝ᵥ x := by
    intro x y
    simp [Matrix.trace, vecMulVec_apply, dotProduct, mul_comm]
  refine ent_of_quad hM d ?_ ?_ ?_
  · intro j
    have h1 := hM.mulVec_eigenvectorBasis j
    set u : n → ℂ := ⇑(hM.eigenvectorBasis j) with hu
    set μ : ℝ := hM.eigenvalues j with hμ
    have hu0 : u ≠ 0 := by
      intro h
      apply (hM.eigenvectorBasis.orthonormal.ne_zero j)
      ext i
      simpa [hu] using congrFun h i
    have h1' : M *ᵥ u = (μ : ℂ) • u := by
      rw [h1, RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
    have ev : (μ : ℂ) * (star v ⬝ᵥ u) =
        (star v ⬝ᵥ v) * (star v ⬝ᵥ u) + (star v ⬝ᵥ w) * (star w ⬝ᵥ u) := by
      have e := congrArg (fun x => star v ⬝ᵥ x) h1'
      simp only [hMv, dotProduct_add, dotProduct_smul, smul_eq_mul] at e
      linear_combination -e
    have ew : (μ : ℂ) * (star w ⬝ᵥ u) =
        (star w ⬝ᵥ v) * (star v ⬝ᵥ u) + (star w ⬝ᵥ w) * (star w ⬝ᵥ u) := by
      have e := congrArg (fun x => star w ⬝ᵥ x) h1'
      simp only [hMv, dotProduct_add, dotProduct_smul, smul_eq_mul] at e
      linear_combination -e
    obtain ⟨q1, q2⟩ := quad_two _ _ _ _ _ _ _ ev ew
    have hquad : ((μ : ℂ) - star v ⬝ᵥ v) * ((μ : ℂ) - star w ⬝ᵥ w) -
        (star v ⬝ᵥ w) * (star w ⬝ᵥ v) = 0 ∨ μ = 0 := by
      by_cases hα : star v ⬝ᵥ u = 0
      · by_cases hβ : star w ⬝ᵥ u = 0
        · right
          have h0 : (μ : ℂ) • u = 0 := by rw [← h1', hMv, hα, hβ]; simp
          rcases smul_eq_zero.mp h0 with h | h
          · exact_mod_cast h
          · exact absurd h hu0
        · left; exact (mul_eq_zero.mp q2).resolve_right hβ
      · left; exact (mul_eq_zero.mp q1).resolve_right hα
    rcases hquad with h | h
    · right
      have h3 : ((μ ^ 2 - μ + d : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination h + (μ : ℂ) * hs - hdet
      exact_mod_cast h3
    · left; exact h
  · rw [hMdef, trace_add, htr, htr]; exact hs
  · have hMM : M * M = vecMulVec (M *ᵥ v) (star v) + vecMulVec (M *ᵥ w) (star w) := by
      nth_rewrite 2 [hMdef]
      rw [Matrix.mul_add, mul_vecMulVec, mul_vecMulVec]
    rw [hMM, trace_add, htr, htr, hMv, hMv]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    push_cast
    linear_combination (star v ⬝ᵥ v + star w ⬝ᵥ w + 1) * hs - 2 * hdet

/-- entropy of a trace-one Hermitian 2x2 matrix via its determinant -/
lemma two_by_two (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (d : ℝ)
    (hs : M 0 0 + M 1 1 = 1) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = (d : ℂ)) :
    QAlgorithms.vnEntropy M = Real.binEntropy ((1 - √(1 - 4 * d)) / 2) / Real.log 2 := by
  refine ent_of_quad hM d ?_ ?_ ?_
  · intro j
    have h1 := hM.mulVec_eigenvectorBasis j
    set u : Fin 2 → ℂ := ⇑(hM.eigenvectorBasis j) with hu
    set μ : ℝ := hM.eigenvalues j with hμ
    have hu0 : u ≠ 0 := by
      intro h
      apply (hM.eigenvectorBasis.orthonormal.ne_zero j)
      ext i
      simpa [hu] using congrFun h i
    have h1' : M *ᵥ u = (μ : ℂ) • u := by
      rw [h1, RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
    have e0 := congrFun h1' 0
    have e1 := congrFun h1' 1
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e0 e1
    obtain ⟨q1, q2⟩ := quad_two (μ : ℂ) (M 0 0) (M 1 1) (M 0 1) (M 1 0) (u 0) (u 1)
      (by linear_combination -e0) (by linear_combination -e1)
    have hquad : ((μ : ℂ) - M 0 0) * ((μ : ℂ) - M 1 1) - M 0 1 * M 1 0 = 0 ∨ μ = 0 := by
      by_cases hα : u 0 = 0
      · by_cases hβ : u 1 = 0
        · exact absurd (funext fun i => by fin_cases i <;> simp [hα, hβ]) hu0
        · left; exact (mul_eq_zero.mp q2).resolve_right hβ
      · left; exact (mul_eq_zero.mp q1).resolve_right hα
    rcases hquad with h | h
    · right
      have h3 : ((μ ^ 2 - μ + d : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination h + (μ : ℂ) * hs - hdet
      exact_mod_cast h3
    · left; exact h
  · rw [Matrix.trace_fin_two]; exact hs
  · rw [Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    linear_combination (M 0 0 + M 1 1 + 1) * hs - 2 * hdet

noncomputable def Q (d : ℝ) : ℝ := Real.binEntropy ((1 - √(1 - 4 * d)) / 2)

noncomputable def W0 (γ : ℝ) {m : ℕ} (x0 x1 : Fin m → ℂ) : Fin m × Fin 2 → ℂ :=
  fun x => if x.2 = 0 then x0 x.1 else ((√(1 - γ) : ℝ) : ℂ) * x1 x.1

noncomputable def W1 (γ : ℝ) {m : ℕ} (x1 : Fin m → ℂ) : Fin m × Fin 2 → ℂ :=
  fun x => if x.2 = 0 then ((√γ : ℝ) : ℂ) * x1 x.1 else 0

lemma W0_0 (γ : ℝ) {m : ℕ} (x0 x1 : Fin m → ℂ) (r : Fin m) : W0 γ x0 x1 (r, 0) = x0 r := by
  simp [W0]
lemma W0_1 (γ : ℝ) {m : ℕ} (x0 x1 : Fin m → ℂ) (r : Fin m) :
    W0 γ x0 x1 (r, 1) = ((√(1 - γ) : ℝ) : ℂ) * x1 r := by
  simp [W0]
lemma W1_0 (γ : ℝ) {m : ℕ} (x1 : Fin m → ℂ) (r : Fin m) :
    W1 γ x1 (r, 0) = ((√γ : ℝ) : ℂ) * x1 r := by
  simp [W1]
lemma W1_1 (γ : ℝ) {m : ℕ} (x1 : Fin m → ℂ) (r : Fin m) : W1 γ x1 (r, 1) = 0 := by
  simp [W1]

lemma tl_herm {α β : Type*} [Fintype α] {M : Matrix (α × β) (α × β) ℂ} (h : M.IsHermitian) :
    (QAlgorithms.traceLeft M).IsHermitian := by
  ext b b'
  simp only [conjTranspose_apply, QAlgorithms.traceLeft, Matrix.of_apply, star_sum]
  exact Finset.sum_congr rfl fun a _ => h.apply _ _

lemma dot_self {m : ℕ} (x : Fin m → ℂ) :
    star x ⬝ᵥ x = ((∑ r, Complex.normSq (x r) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma dot_conj {m : ℕ} (x0 x1 : Fin m → ℂ) :
    (star x0 ⬝ᵥ x1) * (star x1 ⬝ᵥ x0) = ((Complex.normSq (star x0 ⬝ᵥ x1) : ℝ) : ℂ) := by
  have hconj : star x1 ⬝ᵥ x0 = star (star x0 ⬝ᵥ x1) := by
    simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hconj]
  exact Complex.mul_conj _

lemma cs_dot {m : ℕ} (x0 x1 : Fin m → ℂ) :
    Complex.normSq (star x0 ⬝ᵥ x1) ≤ (∑ r, Complex.normSq (x0 r)) * (∑ r, Complex.normSq (x1 r)) := by
  have h1 : ‖star x0 ⬝ᵥ x1‖ ≤ ∑ r, ‖x0 r‖ * ‖x1 r‖ := by
    show ‖∑ r, (star x0) r * x1 r‖ ≤ _
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => ‖x0 r‖) (fun r => ‖x1 r‖)
  have h3 : ∑ r, Complex.normSq (x0 r) = ∑ r, ‖x0 r‖ ^ 2 :=
    Finset.sum_congr rfl fun r _ => (Complex.sq_norm _).symm
  have h4 : ∑ r, Complex.normSq (x1 r) = ∑ r, ‖x1 r‖ ^ 2 :=
    Finset.sum_congr rfl fun r _ => (Complex.sq_norm _).symm
  rw [← Complex.sq_norm, h3, h4]
  calc ‖star x0 ⬝ᵥ x1‖ ^ 2 ≤ (∑ r, ‖x0 r‖ * ‖x1 r‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

open WildeQIT WildeQIT.EADamping in
lemma ad_out_gen (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) {m : ℕ}
    (ψ : EuclideanSpace ℂ (Fin m × Fin 2)) :
    idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity ψ) =
      vecMulVec (W0 γ (fun r => ψ (r, 0)) (fun r => ψ (r, 1)))
        (star (W0 γ (fun r => ψ (r, 0)) (fun r => ψ (r, 1)))) +
      vecMulVec (W1 γ (fun r => ψ (r, 1))) (star (W1 γ (fun r => ψ (r, 1)))) := by
  have hpd : QAlgorithms.pureDensity ψ = vecMulVec (fun x => ψ x) (star (fun x => ψ x)) := by
    ext i j
    simp [QAlgorithms.pureDensity, vecMulVec_apply]
  have h01 : ∀ y : Fin 2, y = 0 ∨ y = 1 := by decide
  rw [hpd, idTensorApply, Fintype.sum_eq_add (show (ampDamp γ hγ).ι from (0 : Fin 2))
    (show (ampDamp γ hγ).ι from (1 : Fin 2)) (by exact (by decide : (0 : Fin 2) ≠ 1))
    (fun x hx => by rcases h01 x with h | h <;> [exact absurd h hx.1; exact absurd h hx.2])]
  simp only [ampDamp]
  rw [conj_rank_one, conj_rank_one]
  congr 2 <;> try congr 1
  all_goals
    funext x
    rcases x with ⟨r, b⟩
    fin_cases b <;>
      simp [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply,
        Matrix.one_apply, W0, W1]

lemma mi_vec (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (x0 x1 : Fin m → ℂ) (pa pb r : ℝ)
    (hA : star x0 ⬝ᵥ x0 = (pa : ℂ)) (hB : star x1 ⬝ᵥ x1 = (pb : ℂ))
    (hC : (star x0 ⬝ᵥ x1) * (star x1 ⬝ᵥ x0) = (r : ℂ)) (hab : pa + pb = 1) :
    DattaDiscord.mutualInfo (vecMulVec (W0 γ x0 x1) (star (W0 γ x0 x1)) +
        vecMulVec (W1 γ x1) (star (W1 γ x1))) =
      (Q (pa * pb - r) + Q ((1 - γ) * ((pa + γ * pb) * pb - r)) -
        Q (γ * ((pa + (1 - γ) * pb) * pb - r))) / Real.log 2 := by
  have hγ0 := hγ.1
  have hγ1 := hγ.2
  have hH : ((√(1 - γ) : ℝ) : ℂ) * ((√(1 - γ) : ℝ) : ℂ) = 1 - (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hG : ((√γ : ℝ) : ℂ) * ((√γ : ℝ) : ℂ) = (γ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hγ0]
  have hsr : star ((√(1 - γ) : ℝ) : ℂ) = ((√(1 - γ) : ℝ) : ℂ) := Complex.conj_ofReal _
  have hsg : star ((√γ : ℝ) : ℂ) = ((√γ : ℝ) : ℂ) := Complex.conj_ofReal _
  have habC : (pa : ℂ) + pb = 1 := by exact_mod_cast hab
  -- Gram entries of the joint output
  have hW00 : star (W0 γ x0 x1) ⬝ᵥ W0 γ x0 x1 = star x0 ⬝ᵥ x0 + (1 - (γ : ℂ)) * (star x1 ⬝ᵥ x1) := by
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, W0_0, W0_1,
      star_mul', hsr]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    linear_combination (star (x1 r) * x1 r) * hH
  have hW11 : star (W1 γ x1) ⬝ᵥ W1 γ x1 = (γ : ℂ) * (star x1 ⬝ᵥ x1) := by
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, W1_0, W1_1,
      star_mul', hsg, star_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    linear_combination (star (x1 r) * x1 r) * hG
  have hW01 : star (W0 γ x0 x1) ⬝ᵥ W1 γ x1 = ((√γ : ℝ) : ℂ) * (star x0 ⬝ᵥ x1) := by
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, W0_0, W0_1,
      W1_0, W1_1, star_mul', hsr]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hW10 : star (W1 γ x1) ⬝ᵥ W0 γ x0 x1 = ((√γ : ℝ) : ℂ) * (star x1 ⬝ᵥ x0) := by
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, W0_0, W0_1,
      W1_0, W1_1, star_mul', hsg, star_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  -- reference marginal
  have hTR : QAlgorithms.traceRight (vecMulVec (W0 γ x0 x1) (star (W0 γ x0 x1)) +
      vecMulVec (W1 γ x1) (star (W1 γ x1))) = vecMulVec x0 (star x0) + vecMulVec x1 (star x1) := by
    ext i j
    simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, Fin.sum_univ_two, W0_0, W0_1, W1_0, W1_1, star_mul', hsr, hsg, star_zero]
    linear_combination (x1 i * star (x1 j)) * (hH + hG)
  -- channel-output marginal entries
  have hT00 : QAlgorithms.traceLeft (vecMulVec (W0 γ x0 x1) (star (W0 γ x0 x1)) +
      vecMulVec (W1 γ x1) (star (W1 γ x1))) 0 0 = star x0 ⬝ᵥ x0 + (γ : ℂ) * (star x1 ⬝ᵥ x1) := by
    simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, dotProduct, W0_0, W1_0, star_mul', hsg]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    linear_combination (star (x1 r) * x1 r) * hG
  have hT11 : QAlgorithms.traceLeft (vecMulVec (W0 γ x0 x1) (star (W0 γ x0 x1)) +
      vecMulVec (W1 γ x1) (star (W1 γ x1))) 1 1 = (1 - (γ : ℂ)) * (star x1 ⬝ᵥ x1) := by
    simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, dotProduct, W0_1, W1_1, star_mul', hsr, star_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    linear_combination (star (x1 r) * x1 r) * hH
  have hT01 : QAlgorithms.traceLeft (vecMulVec (W0 γ x0 x1) (star (W0 γ x0 x1)) +
      vecMulVec (W1 γ x1) (star (W1 γ x1))) 0 1 = ((√(1 - γ) : ℝ) : ℂ) * (star x1 ⬝ᵥ x0) := by
    simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, dotProduct, W0_0, W0_1, W1_0, W1_1, star_mul', hsr, star_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hT10 : QAlgorithms.traceLeft (vecMulVec (W0 γ x0 x1) (star (W0 γ x0 x1)) +
      vecMulVec (W1 γ x1) (star (W1 γ x1))) 1 0 = ((√(1 - γ) : ℝ) : ℂ) * (star x0 ⬝ᵥ x1) := by
    simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.add_apply, vecMulVec_apply,
      Pi.star_apply, dotProduct, W0_0, W0_1, W1_0, W1_1, star_mul', hsr, hsg, star_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [DattaDiscord.mutualInfo, hTR,
    two_vec x0 x1 (pa * pb - r) (by rw [hA, hB]; exact habC)
      (by rw [hA, hB, hC]; push_cast; ring),
    two_by_two _ (tl_herm (herm_two _ _)) ((1 - γ) * ((pa + γ * pb) * pb - r))
      (by rw [hT00, hT11, hA, hB]; linear_combination habC)
      (by
        rw [hT00, hT11, hT01, hT10, hA, hB]
        push_cast
        linear_combination (-(star x1 ⬝ᵥ x0 * (star x0 ⬝ᵥ x1))) * hH - (1 - (γ : ℂ)) * hC),
    two_vec _ _ (γ * ((pa + (1 - γ) * pb) * pb - r))
      (by rw [hW00, hW11, hA, hB]; linear_combination habC)
      (by
        rw [hW00, hW11, hW01, hW10, hA, hB]
        push_cast
        linear_combination (-(star x0 ⬝ᵥ x1 * (star x1 ⬝ᵥ x0))) * hG - (γ : ℂ) * hC)]
  simp only [Q]
  ring

end WildeQIT.EADamping.Aux7e1785ee
namespace WildeQIT.EADamping.C2aux7e1785ee
open Set

/-- equal-length increments of a concave function shrink to the right -/
lemma conc_incr (φ : ℝ → ℝ) (hc : ConcaveOn ℝ (Icc (0 : ℝ) (1 / 4)) φ) {x y h : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hh : 0 ≤ h) (hyh : y + h ≤ 1 / 4) :
    φ (y + h) - φ y ≤ φ (x + h) - φ x := by
  rcases eq_or_lt_of_le (show x ≤ y + h by linarith) with he | hlt
  · have h0 : h = 0 := by linarith
    have hy : y = x := by linarith
    subst h0; subst hy; simp
  set D := y + h - x with hD
  have hDp : 0 < D := by rw [hD]; linarith
  have hxs : x ∈ Icc (0 : ℝ) (1 / 4) := ⟨hx, by linarith⟩
  have hys : y + h ∈ Icc (0 : ℝ) (1 / 4) := ⟨by linarith, hyh⟩
  have ha : 0 ≤ (y - x) / D := div_nonneg (by linarith) hDp.le
  have hb : 0 ≤ h / D := div_nonneg hh hDp.le
  have hab : (y - x) / D + h / D = 1 := by field_simp; rw [hD]; ring
  have hba : h / D + (y - x) / D = 1 := by rw [add_comm]; exact hab
  have c1 := hc.2 hxs hys ha hb hab
  have c2 := hc.2 hxs hys hb ha hba
  simp only [smul_eq_mul] at c1 c2
  have e1 : (y - x) / D * x + h / D * (y + h) = x + h := by field_simp; rw [hD]; ring
  have e2 : h / D * x + (y - x) / D * (y + h) = y := by field_simp; rw [hD]; ring
  rw [e1] at c1; rw [e2] at c2
  have : (y - x) / D * φ x + h / D * φ (y + h) + (h / D * φ x + (y - x) / D * φ (y + h))
      = φ x + φ (y + h) := by
    calc _ = ((y - x) / D + h / D) * φ x + ((y - x) / D + h / D) * φ (y + h) := by ring
      _ = _ := by rw [hab]; ring
  linarith

/-- the monotonicity-in-`r` step of C2, from three properties of the qubit entropy `φ` of the
determinant: monotone, concave, and the scaling inequality -/
lemma chain (φ : ℝ → ℝ) (hm : MonotoneOn φ (Icc (0 : ℝ) (1 / 4)))
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) (1 / 4)) φ)
    (hs : ∀ a b γ : ℝ, 0 ≤ b → b ≤ a → a ≤ 1 / 4 → 0 ≤ γ → γ ≤ 1 →
      φ (γ * a) - φ (γ * b) ≤ φ a - φ b)
    {γ Y0 X0 Z0 r : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hr : 0 ≤ r) (hrY : r ≤ Y0)
    (hYX : Y0 ≤ X0) (hYZ : Y0 ≤ Z0) (hX : γ * X0 ≤ 1 / 4) (hZ : (1 - γ) * Z0 ≤ 1 / 4)
    (hY : Y0 ≤ 1 / 4) :
    φ (Y0 - r) + φ ((1 - γ) * (Z0 - r)) - φ (γ * (X0 - r)) ≤
      φ Y0 + φ ((1 - γ) * Z0) - φ (γ * X0) := by
  have h1γ : 0 ≤ 1 - γ := by linarith
  have h1 : φ ((1 - γ) * (Z0 - r)) ≤ φ ((1 - γ) * Z0) := by
    refine hm ⟨mul_nonneg h1γ (by linarith), ?_⟩ ⟨mul_nonneg h1γ (by linarith), hZ⟩
      (mul_le_mul_of_nonneg_left (by linarith) h1γ)
    nlinarith
  have h2 := conc_incr φ hc (x := γ * (Y0 - r)) (y := γ * (X0 - r)) (h := γ * r)
    (mul_nonneg hγ0 (by linarith)) (mul_le_mul_of_nonneg_left (by linarith) hγ0)
    (mul_nonneg hγ0 hr) (by nlinarith)
  rw [show γ * (X0 - r) + γ * r = γ * X0 by ring,
    show γ * (Y0 - r) + γ * r = γ * Y0 by ring] at h2
  have h3 := hs Y0 (Y0 - r) γ (by linarith) (by linarith) hY hγ0 hγ1
  linarith

/-- qubit entropy (nats) of a density matrix with determinant `d` -/
noncomputable def qe (d : ℝ) : ℝ := Real.binEntropy ((1 - √(1 - 4 * d)) / 2)

/-- `K s = (log(1+s) - log(1-s))/s`, the derivative of `qe` in terms of `s = √(1-4d)` -/
noncomputable def K (s : ℝ) : ℝ := (Real.log (1 + s) - Real.log (1 - s)) / s

lemma K_hasSum {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * s ^ (2 * k)) (K s) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one (x := s)
    (by rw [abs_of_pos h0]; exact h1)).div_const s
  have e : (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * s ^ (2 * k)) =
      fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * s ^ (2 * k + 1) / s := by
    funext k; field_simp <;> ring
  rw [e]; exact h

lemma K_mono : MonotoneOn K (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  refine hasSum_le (fun k => ?_) (K_hasSum hx.1 hx.2) (K_hasSum hy.1 hy.2)
  have : x ^ (2 * k) ≤ y ^ (2 * k) := pow_le_pow_left₀ hx.1.le hxy _
  have hc : (0 : ℝ) ≤ 2 * (1 / (2 * k + 1)) := by positivity
  exact mul_le_mul_of_nonneg_left this hc

lemma qe_hasDerivAt {d : ℝ} (h0 : 0 < d) (h1 : d < 1 / 4) :
    HasDerivAt qe (K (√(1 - 4 * d))) d := by
  set s := √(1 - 4 * d) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs1 : s < 1 := by
    rw [hs, Real.sqrt_lt' one_pos]; nlinarith
  have hlin : HasDerivAt (fun x : ℝ => 1 - 4 * x) (-4) d := by
    simpa using ((hasDerivAt_id d).const_mul 4).const_sub 1
  have hS : HasDerivAt (fun x : ℝ => √(1 - 4 * x)) (-4 / (2 * s)) d :=
    hlin.sqrt (by linarith)
  have hL : HasDerivAt (fun x : ℝ => (1 - √(1 - 4 * x)) / 2) (1 / s) d := by
    exact ((hS.const_sub 1).div_const 2).congr_deriv (by field_simp <;> ring)
  have hB := Real.hasDerivAt_binEntropy (p := (1 - s) / 2) (by linarith) (by linarith)
  have hC := hB.comp d hL
  have e : (Real.log (1 - (1 - s) / 2) - Real.log ((1 - s) / 2)) * (1 / s) = K s := by
    unfold K
    rw [show 1 - (1 - s) / 2 = (1 + s) / 2 by ring, Real.log_div (by linarith) (by norm_num),
      Real.log_div (by linarith) (by norm_num)]
    ring
  exact hC.congr_deriv e

lemma qe_continuous : Continuous qe := by
  unfold qe
  exact Real.binEntropy_continuous.comp (by fun_prop)

lemma qe_concave : ConcaveOn ℝ (Icc (0 : ℝ) (1 / 4)) qe := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) qe_continuous.continuousOn ?_ ?_
  · rw [interior_Icc]; intro d hd
    exact (qe_hasDerivAt hd.1 hd.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx y hy hxy
    rw [(qe_hasDerivAt hx.1 hx.2).deriv, (qe_hasDerivAt hy.1 hy.2).deriv]
    have sx : √(1 - 4 * x) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.sqrt_pos.2 (by linarith [hx.2]), by rw [Real.sqrt_lt' one_pos]; nlinarith [hx.1]⟩
    have sy : √(1 - 4 * y) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.sqrt_pos.2 (by linarith [hy.2]), by rw [Real.sqrt_lt' one_pos]; nlinarith [hy.1]⟩
    exact K_mono sy sx (Real.sqrt_le_sqrt (by linarith))

lemma qe_mono : MonotoneOn qe (Icc (0 : ℝ) (1 / 4)) := by
  intro x hx y hy hxy
  unfold qe
  have hx' : 0 ≤ 1 - 4 * x := by linarith [hx.2]
  have hy' : 0 ≤ 1 - 4 * y := by linarith [hy.2]
  have sx : √(1 - 4 * x) ≤ 1 := by rw [Real.sqrt_le_one]; linarith [hx.1]
  have sy : √(1 - 4 * y) ≤ 1 := by rw [Real.sqrt_le_one]; linarith [hy.1]
  refine Real.binEntropy_strictMonoOn.monotoneOn
    ⟨by linarith, by linarith [Real.sqrt_nonneg (1 - 4 * x)]⟩
    ⟨by linarith, by linarith [Real.sqrt_nonneg (1 - 4 * y)]⟩ ?_
  have := Real.sqrt_le_sqrt (show 1 - 4 * y ≤ 1 - 4 * x by linarith)
  linarith

/-- `(1 - s²) K s` is antitone: it is `2 + Σ (c_{n+1} - c_n) s^{2n+2}` with `c_n = 2/(2n+1)` -/
lemma M_hasSum {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    HasSum (fun n : ℕ => (2 * (1 / (2 * ((n : ℝ) + 1) + 1)) - 2 * (1 / (2 * (n : ℝ) + 1))) *
      s ^ (2 * n + 2)) ((1 - s ^ 2) * K s - 2) := by
  have h := K_hasSum h0 h1
  have hs := (hasSum_nat_add_iff' 1).mpr h
  have hm := h.mul_left (s ^ 2)
  have hd := hs.sub hm
  simp only [Finset.sum_range_one] at hd
  have e : (fun n : ℕ => (2 * (1 / (2 * ((n : ℝ) + 1) + 1)) - 2 * (1 / (2 * (n : ℝ) + 1))) *
      s ^ (2 * n + 2)) = fun n : ℕ => (2 : ℝ) * (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)) *
        s ^ (2 * (n + 1)) - s ^ 2 * ((2 : ℝ) * (1 / (2 * (n : ℝ) + 1)) * s ^ (2 * n)) := by
    funext n; push_cast; ring
  rw [e]
  convert hd using 1 <;> first | rfl | (push_cast; ring) | (norm_num <;> ring) | (simp <;> ring)

lemma M_anti : AntitoneOn (fun s : ℝ => (1 - s ^ 2) * K s) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have := hasSum_le (fun n => ?_) (M_hasSum hy.1 hy.2) (M_hasSum hx.1 hx.2)
  · linarith
  · have hc : 2 * (1 / (2 * ((n : ℝ) + 1) + 1)) - 2 * (1 / (2 * (n : ℝ) + 1)) ≤ 0 := by
      have : 2 * (1 / (2 * ((n : ℝ) + 1) + 1)) ≤ 2 * (1 / (2 * (n : ℝ) + 1)) := by
        gcongr; linarith
      linarith
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx.1.le hxy _) hc

lemma qe_scaling (a b γ : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1 / 4) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) : qe (γ * a) - qe (γ * b) ≤ qe a - qe b := by
  rcases eq_or_lt_of_le hb with hb0 | hbp
  · subst hb0
    simp only [mul_zero, sub_le_sub_iff_right]
    exact qe_mono ⟨mul_nonneg hγ0 (by linarith), by nlinarith⟩ ⟨by linarith, ha⟩
      (by nlinarith)
  have hG : MonotoneOn (fun g : ℝ => qe (g * a) - qe (g * b)) (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((qe_continuous.comp (continuous_id.mul continuous_const)).sub
        (qe_continuous.comp (continuous_id.mul continuous_const))).continuousOn ?_ ?_
    · rw [interior_Icc]; intro g hg
      have ha' : g * a ∈ Ioo (0 : ℝ) (1 / 4) := ⟨by nlinarith [hg.1], by nlinarith [hg.2]⟩
      have hb' : g * b ∈ Ioo (0 : ℝ) (1 / 4) := ⟨by nlinarith [hg.1], by nlinarith [hg.2]⟩
      exact (((qe_hasDerivAt ha'.1 ha'.2).comp g (hasDerivAt_mul_const a)).sub
        ((qe_hasDerivAt hb'.1 hb'.2).comp g (hasDerivAt_mul_const b))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro g hg
      have ha' : g * a ∈ Ioo (0 : ℝ) (1 / 4) := ⟨by nlinarith [hg.1], by nlinarith [hg.2]⟩
      have hb' : g * b ∈ Ioo (0 : ℝ) (1 / 4) := ⟨by nlinarith [hg.1], by nlinarith [hg.2]⟩
      rw [show (fun g : ℝ => qe (g * a) - qe (g * b)) =
          ((qe ∘ fun x => x * a) - qe ∘ fun x => x * b) from rfl,
        (((qe_hasDerivAt ha'.1 ha'.2).comp g (hasDerivAt_mul_const a)).sub
        ((qe_hasDerivAt hb'.1 hb'.2).comp g (hasDerivAt_mul_const b))).deriv]
      set sa := √(1 - 4 * (g * a)) with hsa
      set sb := √(1 - 4 * (g * b)) with hsb
      have sa1 : sa ∈ Ioo (0 : ℝ) 1 :=
        ⟨Real.sqrt_pos.2 (by linarith [ha'.2]), by rw [hsa, Real.sqrt_lt' one_pos]; nlinarith [ha'.1]⟩
      have sb1 : sb ∈ Ioo (0 : ℝ) 1 :=
        ⟨Real.sqrt_pos.2 (by linarith [hb'.2]), by rw [hsb, Real.sqrt_lt' one_pos]; nlinarith [hb'.1]⟩
      have hle : sa ≤ sb := Real.sqrt_le_sqrt (by nlinarith [hg.1])
      have hM := M_anti sa1 sb1 hle
      simp only at hM
      have qa : sa ^ 2 = 1 - 4 * (g * a) := Real.sq_sqrt (by linarith [ha'.2])
      have qb : sb ^ 2 = 1 - 4 * (g * b) := Real.sq_sqrt (by linarith [hb'.2])
      rw [qa, qb] at hM
      have hg0 := hg.1
      nlinarith
  have h := hG ⟨hγ0, hγ1⟩ ⟨zero_le_one, le_refl _⟩ hγ1
  simp only [one_mul] at h
  exact h

/-- the real inequality of C2 (nats): for `ρ' = [[1-p, c], [c̄, p]]` with `|c|² = r` -/
lemma c2_real (γ p r : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r)
    (hrp : r ≤ p * (1 - p)) :
    qe (p * (1 - p) - r) + qe ((1 - γ) * ((1 - (1 - γ) * p) * p - r)) -
        qe (γ * ((1 - γ * p) * p - r)) ≤
      qe (p * (1 - p)) + qe ((1 - γ) * ((1 - (1 - γ) * p) * p)) - qe (γ * ((1 - γ * p) * p)) := by
  have := chain qe qe_mono qe_concave qe_scaling (γ := γ) (Y0 := p * (1 - p))
    (X0 := (1 - γ * p) * p) (Z0 := (1 - (1 - γ) * p) * p) (r := r) hγ0 hγ1 hr hrp
    (by nlinarith [mul_nonneg (mul_nonneg hp0 hp0) (sub_nonneg.2 hγ1)])
    (by nlinarith [mul_nonneg (mul_nonneg hp0 hp0) hγ0]) (by nlinarith [sq_nonneg (γ * p - 1 / 2)])
    (by nlinarith [sq_nonneg ((1 - γ) * p - 1 / 2)]) (by nlinarith [sq_nonneg (p - 1 / 2)])
  have e1 : (1 - γ * p) * p - r = (1 - γ * p) * p - r := rfl
  linarith

end WildeQIT.EADamping.C2aux7e1785ee

namespace WildeQIT.EADamping.Aux7e1785ee
open Matrix WildeQIT.EADamping.C2aux7e1785ee

lemma qe_sq (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : qe (q * (1 - q)) = Real.binEntropy q := by
  unfold qe
  have e : 1 - 4 * (q * (1 - q)) = (1 - 2 * q) ^ 2 := by ring
  rw [e, Real.sqrt_sq_eq_abs]
  rcases le_total q (1 / 2) with h | h
  · rw [abs_of_nonneg (by linarith)]
    congr 1; ring
  · rw [abs_of_nonpos (by linarith), show (1 - -(1 - 2 * q)) / 2 = 1 - q by ring,
      Real.binEntropy_one_sub]

lemma bE (x : ℝ) : WildeQIT.binaryEntropy x = Real.binEntropy x / Real.log 2 := by
  simp only [WildeQIT.binaryEntropy, Real.binEntropy, Real.logb, Real.log_inv]
  ring

open WildeQIT WildeQIT.EADamping in
theorem c2_le_diag (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (φ : WildeQIT.Degradable.PureInput (Fin 2)) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1,
      DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)) ≤
        binaryEntropy p + binaryEntropy ((1 - γ) * p) - binaryEntropy (γ * p) := by
  obtain ⟨m, ψ, hψ⟩ := φ
  obtain ⟨hγ0, hγ1⟩ := hγ
  obtain ⟨pa, hpa⟩ : ∃ pa : ℝ, pa = ∑ r, Complex.normSq (ψ (r, 0)) := ⟨_, rfl⟩
  obtain ⟨pb, hpb⟩ : ∃ pb : ℝ, pb = ∑ r, Complex.normSq (ψ (r, 1)) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Complex.normSq
      (star (fun r => ψ (r, 0)) ⬝ᵥ (fun r => ψ (r, 1))) := ⟨_, rfl⟩
  have hab : pa + pb = 1 := by
    have h2 := hψ
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type] at h2
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib, Complex.sq_norm] at h2
    rw [hpa, hpb]; exact h2
  have hpa0 : 0 ≤ pa := hpa ▸ Finset.sum_nonneg fun r _ => Complex.normSq_nonneg _
  have hpb0 : 0 ≤ pb := hpb ▸ Finset.sum_nonneg fun r _ => Complex.normSq_nonneg _
  have hr0 : 0 ≤ r := hr ▸ Complex.normSq_nonneg _
  have hpa1 : pa = 1 - pb := by linarith
  have hrp : r ≤ pb * (1 - pb) := by
    have h := cs_dot (fun r => ψ (r, 0)) (fun r => ψ (r, 1))
    rw [← hr] at h
    have e : pb * (1 - pb) = (∑ r, Complex.normSq (ψ (r, 0))) * (∑ r, Complex.normSq (ψ (r, 1))) := by
      rw [← hpa, ← hpb, hpa1]; ring
    rw [e]; exact h
  refine ⟨pb, ⟨hpb0, by linarith⟩, ?_⟩
  rw [ad_out_gen γ ⟨hγ0, hγ1⟩ ψ,
    mi_vec γ ⟨hγ0, hγ1⟩ (fun r => ψ (r, 0)) (fun r => ψ (r, 1)) pa pb r
      ((dot_self _).trans (by rw [hpa])) ((dot_self _).trans (by rw [hpb]))
      ((dot_conj _ _).trans (by rw [hr])) hab]
  have key := c2_real γ pb r hγ0 hγ1 hpb0 (by linarith) hr0 hrp
  have hpb1 : pb ≤ 1 := by linarith
  have hq1 : 0 ≤ (1 - γ) * pb := mul_nonneg (by linarith) hpb0
  have hq2 : (1 - γ) * pb ≤ 1 := by nlinarith
  have hq3 : 0 ≤ γ * pb := mul_nonneg hγ0 hpb0
  have hq4 : γ * pb ≤ 1 := by nlinarith
  have r1 : qe (pb * (1 - pb)) = Real.binEntropy pb := qe_sq pb hpb0 hpb1
  have r2 : qe ((1 - γ) * ((1 - (1 - γ) * pb) * pb)) = Real.binEntropy ((1 - γ) * pb) := by
    rw [← qe_sq _ hq1 hq2]; congr 1; ring
  have r3 : qe (γ * ((1 - γ * pb) * pb)) = Real.binEntropy (γ * pb) := by
    rw [← qe_sq _ hq3 hq4]; congr 1; ring
  rw [r1, r2, r3] at key
  have e1 : pa * pb - r = pb * (1 - pb) - r := by rw [hpa1]; ring
  have e2 : (1 - γ) * ((pa + γ * pb) * pb - r) = (1 - γ) * ((1 - (1 - γ) * pb) * pb - r) := by
    rw [hpa1]; ring
  have e3 : γ * ((pa + (1 - γ) * pb) * pb - r) = γ * ((1 - γ * pb) * pb - r) := by
    rw [hpa1]; ring
  have hQ : Q = qe := rfl
  rw [e1, e2, e3, hQ, bE, bE, bE, ← add_div, ← sub_div]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  first
    | exact (div_le_div_iff_of_pos_right hl).mpr key
    | exact div_le_div_of_nonneg_right key hl.le

end WildeQIT.EADamping.Aux7e1785ee

namespace WildeQIT.EADamping.Red7e1785ee
open WildeQIT WildeQIT.EADamping

noncomputable def adObj (γ p : ℝ) : ℝ :=
  binaryEntropy p + binaryEntropy ((1 - γ) * p) - binaryEntropy (γ * p)

def C1_diag_value : Prop :=
  ∀ (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (p : ℝ), p ∈ Set.Icc (0 : ℝ) 1 →
    ∃ φ : WildeQIT.Degradable.PureInput (Fin 2),
      DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)) = adObj γ p

def C2_le_diag : Prop :=
  ∀ (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (φ : WildeQIT.Degradable.PureInput (Fin 2)),
    ∃ p ∈ Set.Icc (0 : ℝ) 1,
      DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)) ≤ adObj γ p

def C3_converse : Prop :=
  ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [Nonempty a]
    (N : QChannel a b) (C : ℝ), IsAchievableEARate N C → C ≤ channelMutualInfo N

def C4_direct : Prop :=
  ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (φ : WildeQIT.Degradable.PureInput a),
    IsAchievableEARate N (DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity φ.ψ)))

lemma binaryEntropy_continuous : Continuous binaryEntropy := by
  have e : binaryEntropy = fun p : ℝ => -((p * Real.log p) / Real.log 2) -
      ((1 - p) * Real.log (1 - p)) / Real.log 2 := by
    funext p; simp only [binaryEntropy, Real.logb]; ring
  rw [e]
  have h := Real.continuous_mul_log
  exact ((h.div_const _).neg).sub ((h.comp (continuous_const.sub continuous_id)).div_const _)

theorem parent_of (h1 : C1_diag_value) (h2 : C2_le_diag) (h3 : C3_converse) (h4 : C4_direct)
    (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest ((fun p : ℝ => binaryEntropy p + binaryEntropy ((1 - γ) * p) -
        binaryEntropy (γ * p)) '' Set.Icc 0 1) (channelMutualInfo (ampDamp γ hγ)) ∧
    IsGreatest (Set.range fun φ : WildeQIT.Degradable.PureInput (Fin 2) =>
        DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)))
      (channelMutualInfo (ampDamp γ hγ)) ∧
    IsLUB {C : ℝ | IsAchievableEARate (ampDamp γ hγ) C} (channelMutualInfo (ampDamp γ hγ)) := by
  set f : ℝ → ℝ := fun p => binaryEntropy p + binaryEntropy ((1 - γ) * p) -
    binaryEntropy (γ * p) with hf
  have hfc : Continuous f := by
    have h := binaryEntropy_continuous
    exact (h.add (h.comp (continuous_const.mul continuous_id))).sub
      (h.comp (continuous_const.mul continuous_id))
  obtain ⟨p0, hp0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1)) hfc.continuousOn
  have hmax' : ∀ p ∈ Set.Icc (0 : ℝ) 1, f p ≤ f p0 := fun p hp => isMaxOn_iff.1 hmax p hp
  set g : WildeQIT.Degradable.PureInput (Fin 2) → ℝ := fun φ =>
    DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)) with hg
  have hgle : ∀ φ, g φ ≤ f p0 := fun φ => by
    obtain ⟨p, hp, hle⟩ := h2 γ hγ φ
    exact hle.trans (hmax' p hp)
  obtain ⟨φ0, hφ0⟩ := h1 γ hγ p0 hp0
  have hφ0' : g φ0 = f p0 := hφ0
  haveI : Nonempty (WildeQIT.Degradable.PureInput (Fin 2)) := ⟨φ0⟩
  have hbdd : BddAbove (Set.range g) := ⟨f p0, by rintro _ ⟨φ, rfl⟩; exact hgle φ⟩
  have hval : channelMutualInfo (ampDamp γ hγ) = f p0 := by
    show (⨆ φ, g φ) = f p0
    apply le_antisymm
    · exact ciSup_le hgle
    · rw [← hφ0']; exact le_ciSup hbdd φ0
  refine ⟨⟨⟨p0, hp0, hval.symm⟩, ?_⟩, ⟨⟨φ0, hφ0'.trans hval.symm⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro _ ⟨p, hp, rfl⟩; rw [hval]; exact hmax' p hp
  · rintro _ ⟨φ, rfl⟩; rw [hval]; exact hgle φ
  · intro C hC; exact h3 _ C hC
  · intro u hu; rw [hval, ← hφ0']; exact hu (h4 _ φ0)


open WildeQIT WildeQIT.EADamping in
/-- clauses 1-2 proved outright (C1, C2); clause 3 from the BSST converse/direct parts C3, C4 -/
theorem parent_from_C3_C4 (h3 : C3_converse) (h4 : C4_direct) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest ((fun p : ℝ => binaryEntropy p + binaryEntropy ((1 - γ) * p) -
        binaryEntropy (γ * p)) '' Set.Icc 0 1) (channelMutualInfo (ampDamp γ hγ)) ∧
    IsGreatest (Set.range fun φ : WildeQIT.Degradable.PureInput (Fin 2) =>
        DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)))
      (channelMutualInfo (ampDamp γ hγ)) ∧
    IsLUB {C : ℝ | IsAchievableEARate (ampDamp γ hγ) C} (channelMutualInfo (ampDamp γ hγ)) :=
  parent_of (fun γ hγ p hp => Aux7e1785ee.c1_diag γ hγ p hp)
    (fun γ hγ φ => Aux7e1785ee.c2_le_diag γ hγ φ) h3 h4 γ hγ

end WildeQIT.EADamping.Red7e1785ee


open WildeQIT WildeQIT.EADamping in
theorem solution (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest ((fun p : ℝ => binaryEntropy p + binaryEntropy ((1 - γ) * p) -
        binaryEntropy (γ * p)) '' Set.Icc 0 1) (channelMutualInfo (ampDamp γ hγ)) ∧
    IsGreatest (Set.range fun φ : WildeQIT.Degradable.PureInput (Fin 2) =>
        DattaDiscord.mutualInfo (idTensorApply (ampDamp γ hγ) (QAlgorithms.pureDensity φ.ψ)))
      (channelMutualInfo (ampDamp γ hγ)) ∧
    IsLUB {C : ℝ | IsAchievableEARate (ampDamp γ hγ) C} (channelMutualInfo (ampDamp γ hγ)) := by
  exact Red7e1785ee.parent_from_C3_C4
    (fun N C hC => isAchievableEARate_le_channelMutualInfo N C hC)
    (fun N φ => pureInput_mutualInfo_isAchievableEARate N φ) γ hγ
