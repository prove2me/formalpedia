-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.cayleyStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:24.018118+00:00
-- url     : https://prove2.me/submissions/3bcf9352-50ac-46f4-8186-397647eda862

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SkewApprox
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Assembly
import Theorems.Thm_PI_UnitaryApproxFinWork_exists_common
import Theorems.Thm_PI_UnitaryApproxFinWork_local_err
import Theorems.Thm_PI_UnitaryApproxFinWork_local_unit
import Theorems.Thm_PI_UnitaryApproxFinWork_MC_cancel
import Theorems.Thm_PI_UnitaryApproxFinWork_MC_entries
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_add
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_adjugate
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_mul
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_one
import Theorems.Thm_PI_UnitaryApproxFinWork_MS_smul
import Theorems.Thm_PI_UnitaryApproxFinWork_algebraMap_mem_intOE
import Theorems.Thm_PI_UnitaryApproxFinWork_cT_map
import Theorems.Thm_PI_UnitaryApproxFinWork_cayley_mem_UJ
import Theorems.Thm_PI_UnitaryApproxFinWork_det_one_add
import Theorems.Thm_PI_UnitaryApproxFinWork_dv_mem_Sv
import Theorems.Thm_PI_UnitaryApproxFinWork_dv_mul
import Theorems.Thm_PI_UnitaryApproxFinWork_dv_two
import Theorems.Thm_PI_UnitaryApproxFinWork_exists_int_mul
import Theorems.Thm_PI_UnitaryApproxFinWork_inclE_mem_Sv
import Theorems.Thm_PI_UnitaryApproxFinWork_lie_of_unitary
import Theorems.Thm_PI_UnitaryApproxFinWork_skew_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : CayleyStep := by
  intro hAE hB hU F E _ _ _ _ _ n _ _ σ J h1 hJ hdet T g hg hP D hD
  classical
  rcases T.eq_empty_or_nonempty with hT | ⟨v0, hv0⟩
  · exact ⟨1, Subgroup.one_mem _, by simp [hT]⟩

  have hJJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hJiH : PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ = J⁻¹ := by
    have hcTJ : PI.UnitaryApproxDefs.cT (σ : E →+* E) J = J := hJ
    have : PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ * J = 1 := by
      calc PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ * J = PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) J := by
            rw [hcTJ]
        _ = PI.UnitaryApproxDefs.cT (σ : E →+* E) (J * J⁻¹) := (PI.UnitaryApproxDefs.cT_mul _ _ _).symm
        _ = 1 := by rw [hJJi, PI.UnitaryApproxDefs.cT_one]
    exact (Matrix.inv_eq_left_inv this).symm
  obtain ⟨cJ, hcJ0, hcJ⟩ := exists_common (F := F) (Finset.univ : Finset (n × n))
    (fun p c => algebraMap F E (c : F) * J⁻¹ p.1 p.2 ∈ PI.UnitaryApproxDefs.intOE E)
    (fun p c r h => by
      rw [show ((c * r : 𝓞 F) : F) = (c : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) c r,
        map_mul, mul_comm (algebraMap F E (c : F)), mul_assoc]
      exact Subring.mul_mem _ (algebraMap_mem_intOE r) h)
    (fun p _ => exists_int_mul (J⁻¹ p.1 p.2))

  obtain ⟨cP, hcP0, hcP⟩ := exists_common (F := F) (T ×ˢ (Finset.univ : Finset (n × n)))
    (fun q c => dv E q.1 c * (1 + (g q.1 : Matrix n n (E ⊗[F] q.1.adicCompletion F))) q.2.1 q.2.2 ∈
      Sv E q.1)
    (fun q c r h => by
      rw [dv_mul, mul_comm (dv E q.1 c), mul_assoc]
      exact Subring.mul_mem _ (dv_mem_Sv _ r) h)
    (fun q _ => hB F E q.1 _)

  obtain ⟨π, hπ0, hπ⟩ := exists_common (F := F) T (fun v c => c ∈ v.asIdeal)
    (fun v c r h => Ideal.mul_mem_right r _ h)
    (fun v _ => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot |>.imp fun c hc => ⟨hc.2, hc.1⟩)
  set e : 𝓞 F := 2 * (cP * D * π) with he
  set δ : 𝓞 F := cJ * cP * e with hδ
  have he0 : e ≠ 0 := mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hcP0 hD) hπ0)
  have hδ0 : δ ≠ 0 := mul_ne_zero (mul_ne_zero hcJ0 hcP0) he0

  let Xl : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F) := fun v =>
    (1 - (g v : Matrix n n _)) * (1 + (g v : Matrix n n _))⁻¹
  have hJR : ∀ v : HeightOneSpectrum (𝓞 F), PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
      (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) = J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
    intro v; rw [cT_map]; rw [show PI.UnitaryApproxDefs.cT (σ : E →+* E) J = J from hJ]
  have hlie : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (Xl v) *
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) +
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v = 0 := fun v hv =>
    lie_of_unitary _ _ _ (hg v hv) (hP v hv)
  have hskew : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
      (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v) =
      -(J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v) := by
    intro v hv
    rw [PI.UnitaryApproxDefs.cT_mul, hJR]
    exact eq_neg_of_add_eq_zero_left (hlie v hv)
  obtain ⟨Y', hY'skew, hY'⟩ := skew_approx hAE σ h1 T
    (fun v => J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v) hskew δ hδ0

  set X' : Matrix n n E := J⁻¹ * Y' with hX'
  have hX'lie : PI.UnitaryApproxDefs.cT (σ : E →+* E) X' * J + J * X' = 0 := by
    rw [hX', PI.UnitaryApproxDefs.cT_mul, hJiH, hY'skew, Matrix.mul_assoc, hJiJ, Matrix.mul_one, ← Matrix.mul_assoc,
      hJJi, Matrix.one_mul, neg_add_cancel]

  have hloc : ∀ v ∈ T, ∃ W N : Matrix n n (E ⊗[F] v.adicCompletion F),
      (1 + Xl v) * (1 + (g v : Matrix n n _)) = 2 ∧
      (X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) - Xl v) * (1 + (g v : Matrix n n _)) =
        (2 : E ⊗[F] v.adicCompletion F) • W ∧
      (1 + W) * N = 1 ∧ IsUnit (1 + W).det ∧ MC E v D ((1 + (g v : Matrix n n _)) * W * N) := by
    intro v hv
    set ι : E →+* E ⊗[F] v.adicCompletion F := PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) with hι
    set P : Matrix n n (E ⊗[F] v.adicCompletion F) := 1 + (g v : Matrix n n _) with hPdef
    have hXP : (1 + Xl v) * P = 2 := by
      show (1 + (1 - (g v : Matrix n n _)) * P⁻¹) * P = 2
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hP v hv),
        Matrix.mul_one, hPdef]
      rw [← one_add_one_eq_two]
      abel
    have hJiJR : J⁻¹.map ι * J.map ι = 1 := by
      rw [← Matrix.map_mul, hJiJ, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have hXR : X'.map ι = J⁻¹.map ι * Y'.map ι := by rw [hX', Matrix.map_mul]
    obtain ⟨A, hAS, hAeq⟩ := hY' v hv
    have hAeq' : Y'.map ι - J.map ι * Xl v = dv E v δ • A := hAeq
    have hΔ1 : X'.map ι - Xl v = J⁻¹.map ι * (Y'.map ι - J.map ι * Xl v) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hJiJR, Matrix.one_mul, hXR]
    set B : Matrix n n (E ⊗[F] v.adicCompletion F) := dv E v cJ • J⁻¹.map ι with hBdef
    have hBS : MS E v B := fun i j => by
      rw [hBdef, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, hι, dv, ← map_mul]
      exact inclE_mem_Sv v (hcJ (i, j) (Finset.mem_univ _))
    set P' : Matrix n n (E ⊗[F] v.adicCompletion F) := dv E v cP • P with hP'def
    have hP'S : MS E v P' := fun i j => by
      rw [hP'def, Matrix.smul_apply, smul_eq_mul]
      exact hcP (v, (i, j)) (Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩)
    have hc : dv E v (cJ * cP) • ((X'.map ι - Xl v) * P) = dv E v (cJ * cP * e) • (B * A * P') := by
      rw [hΔ1, hAeq', hBdef, hP'def, hδ]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, dv_mul]
      congr 1
      ring
    have hΔP := MC_cancel (mul_ne_zero hcJ0 hcP0) hc
    set W1 : Matrix n n (E ⊗[F] v.adicCompletion F) := dv E v (cP * D) • (B * A * P') with hW1def
    have hW1S : MS E v W1 := MS_smul (dv_mem_Sv v _) (MS_mul (MS_mul hBS hAS) hP'S)
    obtain ⟨s, hs, hdet1⟩ := det_one_add π hW1S
    obtain ⟨u, hu, hu1⟩ := hU F E v π (hπ v hv) s hs
    refine ⟨dv E v π • W1, u • (1 + dv E v π • W1).adjugate, hXP, ?_, ?_, ?_, ?_⟩
    · rw [hΔP, he, hW1def, dv_mul, dv_two, dv_mul v (cP * D) π]
      simp only [smul_smul]
      congr 1
      ring
    · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet1, smul_smul, mul_comm u, hu1, one_smul]
    · rw [hdet1]; exact IsUnit.of_mul_eq_one _ hu1
    · refine ⟨(dv E v π • (P' * (B * A * P'))) * (u • (1 + dv E v π • W1).adjugate),
        MS_mul (MS_smul (dv_mem_Sv v π) (MS_mul hP'S (MS_mul (MS_mul hBS hAS) hP'S)))
          (MS_smul hu (MS_adjugate (MS_add MS_one (MS_smul (dv_mem_Sv v π) hW1S)))), ?_⟩
      rw [hW1def, hP'def]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, dv_mul]
      congr 1
      ring
  have h2u : ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (2 : E ⊗[F] v.adicCompletion F) := by
    intro v
    have := (IsUnit.mk0 (2 : E) two_ne_zero).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
    rwa [map_ofNat] at this

  have hQ : IsUnit (1 + X').det := by
    obtain ⟨W, N, hXP, hΔ, -, hWu, -⟩ := hloc v0 hv0
    have hl := local_unit (h2u v0) _ _ _ _ hXP hΔ hWu
    have hmap : (1 + X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v0.adicCompletion F))).det =
        PI.UnitaryApproxDefs.inclE (F := F) (v0.adicCompletion F) (1 + X').det := by
      rw [RingHom.map_det, map_add, map_one]; rfl
    rw [hmap] at hl
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, map_zero, isUnit_zero_iff] at hl
    have hinj : Function.Injective (PI.UnitaryApproxDefs.inclE (F := F) (v0.adicCompletion F) : E → _) :=
      Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := E)
        (B := v0.adicCompletion F) (algebraMap F _).injective
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hl))
  obtain ⟨γ, hγU, hγ⟩ := cayley_mem_UJ (σ : E →+* E) J X' hdet hX'lie hQ
  refine ⟨γ, hγU, fun v hv i j => ?_⟩
  obtain ⟨W, N, hXP, hΔ, hN, -, hMC⟩ := hloc v hv
  have hγQ : (γ : Matrix n n E) * (1 + X') = 1 - X' := by
    rw [hγ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one]
  have hγR : (γ : Matrix n n E).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) *
      (1 + X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      1 - X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
    have := congrArg (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)).mapMatrix hγQ
    simpa [map_mul, map_add, map_sub, map_one] using this
  have herr := local_err (h2u v) _ _ _ _ _ _ hXP hΔ hN hγR
  rw [← herr] at hMC
  exact MC_entries hMC i j
end PI.UnitaryApproxFinWork
