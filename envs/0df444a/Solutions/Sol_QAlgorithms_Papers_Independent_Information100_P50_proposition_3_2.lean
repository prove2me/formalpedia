-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P50.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:45:04.373137+00:00
-- url     : https://prove2.me/submissions/beca4e4b-808d-4854-b1b2-f0f6592d1dfa

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

open scoped Matrix ComplexOrder Topology
open Filter

namespace G54

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma spec_nonneg {C : Matrix I I ℂ} (hC : C.PosSemidef) : ∀ t ∈ spectrum ℝ C, 0 ≤ t := by
  intro t ht
  rw [hC.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hC.eigenvalues_nonneg i

lemma shift_eq {C : Matrix I I ℂ} (hC : C.PosSemidef) (e : ℝ) :
    C + (e : ℂ) • (1 : Matrix I I ℂ) = cfc (fun t : ℝ => t + e) C := by
  have hsa : IsSelfAdjoint C := hC.isHermitian
  rw [cfc_add_const e (fun t => t) C, cfc_id' ℝ C, Algebra.algebraMap_eq_smul_one]
  congr 1


lemma cfc_shift {C : Matrix I I ℂ} (hC : C.PosSemidef) (e : ℝ) (f : ℝ → ℝ) :
    cfc f (C + (e : ℂ) • (1 : Matrix I I ℂ)) = cfc (fun t => f (t + e)) C := by
  have hsa : IsSelfAdjoint C := hC.isHermitian
  rw [shift_eq hC e]
  have hfin : ((fun t : ℝ => t + e) '' spectrum ℝ C).Finite :=
    C.finite_real_spectrum.image _
  exact (cfc_comp' f (fun t : ℝ => t + e) C (hfin.continuousOn _)).symm

/-- the R · sqrt(Q A Q) · R product with B = C + e (R = sqrt B, Q = B^{-1/2}). -/
noncomputable def persp (f : ℝ → ℝ) (A B : Matrix I I ℂ) : Matrix I I ℂ :=
  let R := cfc Real.sqrt B
  let Q := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) B
  R * cfc f (Q * A * Q) * R

lemma persp_self {C : Matrix I I ℂ} (hC : C.PosSemidef) {e : ℝ} (he : 0 < e) :
    persp Real.sqrt (C + (e : ℂ) • 1) (C + (e : ℂ) • 1) = C + (e : ℂ) • 1 := by
  have hsa : IsSelfAdjoint C := hC.isHermitian
  have hfin := C.finite_real_spectrum
  unfold persp
  simp only
  rw [cfc_shift hC e, cfc_shift hC e]
  conv_lhs => rw [show C + (e : ℂ) • (1 : Matrix I I ℂ) = cfc (fun t : ℝ => t + e) C from shift_eq hC e]
  rw [← cfc_mul (fun t => (Real.sqrt (t + e))⁻¹) (fun t : ℝ => t + e) C (hfin.continuousOn _)
    (hfin.continuousOn _)]
  rw [← cfc_mul _ (fun t => (Real.sqrt (t + e))⁻¹) C (hfin.continuousOn _) (hfin.continuousOn _)]
  have h1 : cfc (fun t => (Real.sqrt (t + e))⁻¹ * (t + e) * (Real.sqrt (t + e))⁻¹) C =
      cfc (fun _ : ℝ => (1 : ℝ)) C := by
    apply cfc_congr
    intro t ht
    have ht0 : 0 < t + e := by linarith [spec_nonneg hC t ht]
    have hs := Real.sq_sqrt ht0.le
    have hs0 : 0 < Real.sqrt (t + e) := Real.sqrt_pos.mpr ht0
    field_simp
    nlinarith
  rw [h1, cfc_const (1 : ℝ) C, map_one]
  rw [show (1 : Matrix I I ℂ) = algebraMap ℝ (Matrix I I ℂ) 1 from (map_one _).symm,
    cfc_algebraMap, Real.sqrt_one, map_one, mul_one]
  rw [← cfc_mul _ _ C (hfin.continuousOn _) (hfin.continuousOn _), shift_eq hC e]
  apply cfc_congr
  intro t ht
  have ht0 : 0 ≤ t + e := by linarith [spec_nonneg hC t ht]
  exact Real.mul_self_sqrt ht0

lemma persp_zero {C : Matrix I I ℂ} (hC : C.PosSemidef) {e : ℝ} (he : 0 < e) :
    persp Real.sqrt ((0 : Matrix I I ℂ) + (e : ℂ) • 1) (C + (e : ℂ) • 1) =
      cfc (fun t => Real.sqrt e * Real.sqrt (t + e)) C := by
  have hsa : IsSelfAdjoint C := hC.isHermitian
  have hfin := C.finite_real_spectrum
  unfold persp
  simp only
  rw [cfc_shift hC e, cfc_shift hC e, zero_add]
  have hQ : cfc (fun t => (Real.sqrt (t + e))⁻¹) C * ((e : ℂ) • 1) *
      cfc (fun t => (Real.sqrt (t + e))⁻¹) C =
      cfc (fun t => e * ((Real.sqrt (t + e))⁻¹ * (Real.sqrt (t + e))⁻¹)) C := by
    rw [cfc_const_mul e _ C (hfin.continuousOn _), cfc_mul _ _ C (hfin.continuousOn _) (hfin.continuousOn _),
      Matrix.mul_smul, mul_one, Matrix.smul_mul]
    rw [← Complex.coe_smul]
  rw [hQ]
  have hfin2 : ((fun t => e * ((Real.sqrt (t + e))⁻¹ * (Real.sqrt (t + e))⁻¹)) ''
      spectrum ℝ C).Finite := hfin.image _
  rw [← cfc_comp' Real.sqrt _ C (hfin2.continuousOn _) (hfin.continuousOn _)]
  rw [← cfc_mul _ _ C (hfin.continuousOn _) (hfin.continuousOn _),
    ← cfc_mul _ _ C (hfin.continuousOn _) (hfin.continuousOn _)]
  apply cfc_congr
  intro t ht
  have ht0 : 0 < t + e := by linarith [spec_nonneg hC t ht]
  have hs0 : 0 < Real.sqrt (t + e) := Real.sqrt_pos.mpr ht0
  simp only
  rw [Real.sqrt_mul he.le, Real.sqrt_mul_self (inv_nonneg.mpr hs0.le)]
  field_simp

end G54

noncomputable section
open scoped ComplexConjugate
open QAlgorithms
attribute [local instance] Classical.decEq Classical.propDecidable
open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26
theorem g52b_choi_apply {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (o o' : O) (i i' : I) :
    outputFirstChoi M (o, i) (o', i') = M (Matrix.single i i' 1) o o' := rfl

theorem g52b_lin_expand {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g52b_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g52b_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g52b_cp_of_choi {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (outputFirstChoi M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    rw [← g52b_choi_apply, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g52b_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g52b_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g52b_sum_psd _ _ fun a => g52b_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _


end

noncomputable section
open scoped Matrix ComplexOrder Topology
open Filter QAlgorithms QAlgorithms.Papers.Independent.Information100.P50

theorem g54_cp_add {I J : Type*} [Fintype I] [Fintype J] (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hΦ : Entanglement.IsCompletelyPositive Φ) (hΨ : Entanglement.IsCompletelyPositive Ψ) :
    Entanglement.IsCompletelyPositive (Φ + Ψ) := by
  intro r X hX
  have : idTensorSuperop (⇑(Φ + Ψ)) X = idTensorSuperop Φ X + idTensorSuperop Ψ X := by
    ext p q; rfl
  rw [this]; exact (hΦ r X hX).add (hΨ r X hX)

theorem g54_cp_zero {I J : Type*} [Fintype I] [Fintype J] :
    Entanglement.IsCompletelyPositive (0 : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) := by
  intro r X _
  have h : idTensorSuperop (0 : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) X = 0 := rfl
  rw [h]
  exact Matrix.PosSemidef.zero

theorem g54_tendsto_zero {I : Type*} [Fintype I] [DecidableEq I] {C : Matrix I I ℂ}
    (hC : C.PosSemidef) :
    Tendsto (fun e : ℝ => cfc (fun t => Real.sqrt e * Real.sqrt (t + e)) C) (𝓝 0) (𝓝 0) := by
  have hH := hC.isHermitian
  simp only [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hc : Continuous (fun e : ℝ => (hH.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ (fun t => Real.sqrt e * Real.sqrt (t + e)) ∘ hH.eigenvalues) *
      star (hH.eigenvectorUnitary : Matrix I I ℂ)) := by
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    simp only [Function.comp]
    fun_prop
  have := hc.tendsto 0
  convert this using 2
  simp [Function.comp_def]

theorem g54_density_exists {n : ℕ} (hn : 0 < n) :
    ∃ rho : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityMatrix rho := by
  refine ⟨Matrix.diagonal (Pi.single (⟨0, hn⟩, ⟨0, hn⟩) 1), ?_, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    by_cases h : i = (⟨0, hn⟩, ⟨0, hn⟩)
    · subst h; simp
    · simp [Pi.single_apply, h]
  · rw [Matrix.trace_diagonal]
    simp

theorem g54_gm_zero {I : Type*} [Fintype I] [DecidableEq I] {C : Matrix I I ℂ}
    (hC : C.PosSemidef) : geometricMean C 0 = 0 := by
  unfold geometricMean regularizedPerspective
  apply Tendsto.limUnder_eq
  have h := (g54_tendsto_zero hC).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (G54.persp_zero hC he).symm

theorem g54_gm_self {I : Type*} [Fintype I] [DecidableEq I] {C : Matrix I I ℂ}
    (hC : C.PosSemidef) : geometricMean C C = C := by
  unfold geometricMean regularizedPerspective
  apply Tendsto.limUnder_eq
  have hc : Continuous (fun e : ℝ => C + (e : ℂ) • (1 : Matrix I I ℂ)) := by fun_prop
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (G54.persp_self hC he).symm

theorem solution {dx dy : ℕ} (hdx : 0 < dx) (hdy : 2 ≤ dy) :
    ∃ Phi1 Psi1 Phi2 Psi2 : Lin dx dy,
      Entanglement.IsCompletelyPositive Phi1 ∧ Entanglement.IsCompletelyPositive Psi1 ∧
      Entanglement.IsCompletelyPositive Phi2 ∧ Entanglement.IsCompletelyPositive Psi2 ∧
      Phi1 + Psi1 = Phi2 + Psi2 ∧ geometricFidelity Phi1 Psi1 = 0 ∧
      geometricFidelity Phi2 Psi2 = 1 := by
  have hdy0 : (dy : ℂ) ≠ 0 := by exact_mod_cast (by omega : dy ≠ 0)
  set c : ℂ := (dy : ℂ)⁻¹ with hc
  let T : Lin dx dy := (Matrix.traceLinearMap (Fin dx) ℂ ℂ).smulRight (c • (1 : M dy))
  have hT : ∀ A, T A = (A.trace * c) • (1 : M dy) := fun A => by
    simp [T, smul_smul]
  have hTcp : Entanglement.IsCompletelyPositive T := by
    apply g52b_cp_of_choi
    have : QAlgorithms.Papers.Independent.Dependency50.P26.outputFirstChoi T =
        c • (1 : Matrix (Fin dy × Fin dx) (Fin dy × Fin dx) ℂ) := by
      ext ⟨o, i⟩ ⟨o', i'⟩
      rw [g52b_choi_apply, hT]
      by_cases hi : i = i'
      · subst hi
        by_cases ho : o = o' <;> simp [ho, Matrix.one_apply]
      · simp [hi, Matrix.one_apply, Matrix.trace_single_eq_of_ne _ _ _ hi]
    rw [this]
    refine Matrix.PosSemidef.one.smul ?_
    rw [hc, show ((dy : ℂ))⁻¹ = (((dy : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.mpr (by positivity)
  have htr : ∀ rho : Matrix (Fin dx × Fin dx) (Fin dx × Fin dx) ℂ,
      (amplify T dx rho).trace = rho.trace := by
    intro rho
    unfold amplify idTensorSuperop
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, hT, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hc]; field_simp
  refine ⟨T + T, 0, T, T, g54_cp_add _ _ hTcp hTcp, g54_cp_zero, hTcp, hTcp, by simp, ?_, ?_⟩
  · unfold geometricFidelity
    have hset : {v : ℝ | ∃ rho : Matrix (Fin dx × Fin dx) (Fin dx × Fin dx) ℂ,
        IsDensityMatrix rho ∧ v = (geometricMean (amplify (T + T) dx rho)
          (amplify (0 : Lin dx dy) dx rho)).trace.re} = {0} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rho, hrho, rfl⟩
        have h0 : amplify (0 : Lin dx dy) dx rho = 0 := rfl
        rw [h0, g54_gm_zero (show (amplify (T + T) dx rho).PosSemidef from g54_cp_add _ _ hTcp hTcp dx rho hrho.1)]
        simp
      · rintro rfl
        obtain ⟨rho, hrho⟩ := g54_density_exists hdx
        refine ⟨rho, hrho, ?_⟩
        have h0 : amplify (0 : Lin dx dy) dx rho = 0 := rfl
        rw [h0, g54_gm_zero (show (amplify (T + T) dx rho).PosSemidef from g54_cp_add _ _ hTcp hTcp dx rho hrho.1)]
        simp
    rw [hset, csInf_singleton]
  · unfold geometricFidelity
    have hset : {v : ℝ | ∃ rho : Matrix (Fin dx × Fin dx) (Fin dx × Fin dx) ℂ,
        IsDensityMatrix rho ∧ v = (geometricMean (amplify T dx rho)
          (amplify T dx rho)).trace.re} = {1} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rho, hrho, rfl⟩
        rw [g54_gm_self (show (amplify T dx rho).PosSemidef from hTcp dx rho hrho.1), htr, hrho.2]
        simp
      · rintro rfl
        obtain ⟨rho, hrho⟩ := g54_density_exists hdx
        refine ⟨rho, hrho, ?_⟩
        rw [g54_gm_self (show (amplify T dx rho).PosSemidef from hTcp dx rho hrho.1), htr, hrho.2]
        simp
    rw [hset, csInf_singleton]

end
