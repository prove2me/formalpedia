-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_localProduct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:49:40.130504+00:00
-- url     : https://prove2.me/submissions/f59a1f1a-b1d0-41c0-8118-a45b772733ba

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)


theorem g53a_trace_kraus {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (N : Superop I J) (hN : IsChannel N) (X : Matrix I I ℂ) : (N X).trace = X.trace := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  rw [hNE, krausApply, Matrix.trace_sum]
  have : ∀ k, (E k * X * (E k)ᴴ).trace = ((E k)ᴴ * E k * X).trace := fun k => by
    rw [Matrix.trace_mul_cycle]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ k, (E k)ᴴ * E k) = 1 from hE, one_mul]

theorem g53a_trace_choi {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (N : Superop I J) (hN : IsChannel N) : (choi N).trace = (Fintype.card I : ℂ) := by
  have h1 : (choi N).trace = ∑ i : I, (N (Matrix.single i i 1)).trace := by
    simp only [Matrix.trace, Matrix.diag, choi, Fintype.sum_prod_type]
  rw [h1]
  simp_rw [g53a_trace_kraus N hN]
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply]

theorem g53a_re_trace_nonneg {I : Type} [Fintype I] {X : Matrix I I ℂ} (h : X.PosSemidef) :
    0 ≤ X.trace.re := by
  have := h.trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

theorem g53a_entry_le_specNorm {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (i : I) :
    ‖M i i‖ ≤ specNorm M := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single i (1 : ℂ))
  have h2 : ‖M i i‖ ≤ ‖(WithLp.toLp 2 (M *ᵥ (WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)))) :
      EuclideanSpace ℂ I)‖ := by
    have := PiLp.norm_apply_le (p := 2) (WithLp.toLp 2 (M *ᵥ (WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)))) :
      EuclideanSpace ℂ I) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have h3 : ‖(EuclideanSpace.single i (1 : ℂ))‖ = 1 := by simp
  rw [h3, mul_one] at h
  exact le_trans h2 h

theorem g53a_re_trace_le {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) :
    M.trace.re ≤ (Fintype.card I : ℝ) * specNorm M := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ i, (M.diag i).re ≤ ∑ _i : I, specNorm M := by
        apply Finset.sum_le_sum; intro i _
        exact le_trans (Complex.re_le_norm _) (g53a_entry_le_specNorm M i)
    _ = _ := by simp

theorem g53a_one_le_beta {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B]
    (N : Superop (A × B) (C × D)) (htr : (choi N).trace = (Fintype.card (A × B) : ℂ)) :
    (1 : EReal) ≤ bipartiteBeta N := by
  apply le_sInf
  rintro r ⟨S, V, hF, rfl⟩
  obtain ⟨_, _, _, hVm, _, hSm, _⟩ := hF
  have e1 := g53a_re_trace_nonneg hSm
  have e2 := g53a_re_trace_nonneg hVm
  have htb : ∀ X : Op ((A × B) × (C × D)), (transposeBobChoi X).trace = X.trace := fun X => rfl
  rw [htb, Matrix.trace_sub, Complex.sub_re, htr] at e2
  rw [Matrix.trace_sub, Complex.sub_re] at e1
  have e3 : (traceOutput S).trace = S.trace := by
    simp only [Matrix.trace, Matrix.diag, traceOutput, Fintype.sum_prod_type]
  have e4 := g53a_re_trace_le (traceOutput S)
  rw [e3] at e4
  simp only [Complex.natCast_re] at e2
  have hpos : (0 : ℝ) < (Fintype.card (A × B) : ℝ) := by exact_mod_cast Fintype.card_pos
  have : (1 : ℝ) ≤ specNorm (traceOutput S) := by
    by_contra hc
    push Not at hc
    nlinarith
  exact_mod_cast this


def g53a_sig (A B C D : Type) : ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem g53a_tensor_single {A B C D : Type} [Fintype A] [Fintype B]
    (E : Superop A C) (F : Superop B D) (a aa : A) (b bb : B) (p q : C × D) :
    tensorAction E F (Matrix.single (a, b) (aa, bb) 1) p q =
      E (Matrix.single a aa 1) p.1 q.1 * F (Matrix.single b bb 1) p.2 q.2 := by
  simp only [tensorAction]
  rw [Fintype.sum_eq_single a (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single aa (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single b (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  rw [Fintype.sum_eq_single bb (fun x hx => by simp [Matrix.single_apply, Ne.symm hx])]
  simp [Matrix.single_apply]

theorem g53a_choi_tensor {A B C D : Type} [Fintype A] [Fintype B]
    (E : Superop A C) (F : Superop B D) :
    choi (tensorAction E F) =
      (Matrix.kronecker (choi E) (choi F)).submatrix (g53a_sig A B C D) (g53a_sig A B C D) := by
  ext p q
  simp only [choi, Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, g53a_sig,
    Equiv.coe_fn_mk]
  exact g53a_tensor_single E F _ _ _ _ _ _

theorem g53a_choi_psd {I J : Type} [Fintype I] [Fintype J] (E : Superop I J) (hE : IsChannel E) :
    (choi E).PosSemidef := by
  obtain ⟨m, K, _, hK⟩ := hE
  have : choi E = ∑ k, Matrix.vecMulVec (fun p : I × J => K k p.2 p.1)
      (star (fun p : I × J => K k p.2 p.1)) := by
    ext p q
    simp only [choi, hK, krausApply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_eq_single q.1 (fun j hj => by simp [Ne.symm hj])]
    rw [Fintype.sum_eq_single p.1 (fun j hj => by simp [Ne.symm hj])]
    simp
  rw [this]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h1 h2 => h1.add h2)
    Matrix.PosSemidef.zero (fun k _ => Matrix.posSemidef_vecMulVec_self_star _)

theorem g53a_choi_ptrace {I J : Type} [Fintype I] [Fintype J] (E : Superop I J) (hE : IsChannel E)
    (a aa : I) : ∑ c : J, choi E (a, c) (aa, c) = if a = aa then 1 else 0 := by
  have := g53a_trace_kraus E hE (Matrix.single a aa 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [choi]
  rw [this]
  by_cases h : a = aa
  · subst h; simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h, Ne.symm h]

theorem g53a_lp_beta_le {A B C D : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Fintype D]
    (E : Superop A C) (F : Superop B D) (hE : IsChannel E) (hF : IsChannel F) :
    bipartiteBeta (tensorAction E F) ≤ 1 ∧
      (choi (tensorAction E F)).trace = (Fintype.card (A × B) : ℂ) := by
  have hJ := g53a_choi_tensor E F
  have hpE := g53a_choi_psd E hE
  have hpF := g53a_choi_psd F hF
  have hJpsd : (choi (tensorAction E F)).PosSemidef := by
    rw [hJ]; exact (hpE.kronecker hpF).submatrix _
  have htb : transposeBobChoi (choi (tensorAction E F)) =
      (Matrix.kronecker (choi E) (choi F).transpose).submatrix (g53a_sig A B C D) (g53a_sig A B C D) := by
    rw [hJ]; ext p q; rfl
  have htbpsd : (transposeBobChoi (choi (tensorAction E F))).PosSemidef := by
    rw [htb]; exact (hpE.kronecker hpF.transpose).submatrix _
  have hadd : ∀ X Y : Op ((A × B) × (C × D)),
      transposeBobChoi (X + Y) = transposeBobChoi X + transposeBobChoi Y := by
    intro X Y; ext p q; rfl
  have hz : transposeBobChoi (0 : Op ((A × B) × (C × D))) = 0 := by ext p q; rfl
  have hto : traceOutput (choi (tensorAction E F)) = 1 := by
    rw [hJ]
    ext i j
    show (∑ x : C × D, choi E (i.1, x.1) (j.1, x.1) * choi F (i.2, x.2) (j.2, x.2)) =
      (1 : Op (A × B)) i j
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp_rw [← Finset.sum_mul]
    rw [g53a_choi_ptrace E hE, g53a_choi_ptrace F hF, Matrix.one_apply]
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;> simp [h1, h2]
  have hns : ChoiNS (choi (tensorAction E F)) := by
    intro a aa b bb d dd
    rw [hJ]
    simp only [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      g53a_sig, Equiv.coe_fn_mk]
    simp_rw [← Finset.sum_mul]
    rw [g53a_choi_ptrace E hE]
    simp_rw [g53a_choi_ptrace E hE]
    simp only [if_true, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card A : ℂ) ≠ 0 := by
      have : 0 < Fintype.card A := Fintype.card_pos
      exact_mod_cast this.ne'
    by_cases h : a = aa
    · simp [h]
    · simp [h]
  constructor
  · apply sInf_le
    refine ⟨choi (tensorAction E F), choi (tensorAction E F), ⟨hJpsd.isHermitian, hJpsd.isHermitian,
      ?_, ?_, hJpsd.add hJpsd, ?_, hns⟩, ?_⟩
    · rw [hadd]; exact htbpsd.add htbpsd
    · rw [sub_self, hz]; exact Matrix.PosSemidef.zero
    · rw [sub_self]; exact Matrix.PosSemidef.zero
    · rw [hto]
      have e : specNorm (1 : Op (A × B)) =
        ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := A × B) (n := A × B)).trans LinearMap.toContinuousLinearMap
          (1 : Op (A × B))‖ := rfl
      rw [e]
      have : (Matrix.toEuclideanLin (𝕜 := ℂ) (m := A × B) (n := A × B)).trans
          LinearMap.toContinuousLinearMap (1 : Op (A × B)) = ContinuousLinearMap.id ℂ _ := by
        ext x; simp
      rw [this, ContinuousLinearMap.norm_id]
      rfl
  · have : (choi (tensorAction E F)).trace = (traceOutput (choi (tensorAction E F))).trace := by
      simp only [Matrix.trace, Matrix.diag, traceOutput, Fintype.sum_prod_type]
    rw [this, hto, Matrix.trace_one]

end QAlgorithms.Papers.Independent.Dependency50.P09

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P09
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 5 (Zero on tensor product of local channels), arXiv:2010.01058v3, PDF pp.6.
 -/
theorem solution {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (E : Superop A C) (F : Superop B D) (hE : IsChannel E) (hF : IsChannel F) :
    cBeta (tensorAction E F) = 0 := by
  obtain ⟨h2, htr⟩ := g53a_lp_beta_le E F hE hF
  have h1 := g53a_one_le_beta (tensorAction E F) htr
  have : bipartiteBeta (tensorAction E F) = 1 := le_antisymm h2 h1
  unfold cBeta logExt
  rw [this, if_neg (show (1:EReal) ≠ ⊤ from EReal.coe_ne_top 1),
    if_neg (show ¬ (1:EReal) ≤ 0 from not_le.mpr zero_lt_one)]
  simp


end

