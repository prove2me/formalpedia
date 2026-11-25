-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.vMod_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:24.792007+00:00
-- url     : https://prove2.me/submissions/2a3698d1-0543-4e2f-aec2-1cf09546eb1a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_BVRApply
import Theorems.Thm_PI_VolSemiDirect_W_Cj_bVR_apply
import Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_expand
import Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_lin
import Theorems.Thm_PI_VolSemiDirect_W_Lc_finite_nf
import Theorems.Thm_PI_VolSemiDirect_W_Lc_tensor_adele_topology_holds
import Theorems.Thm_PI_VolStabSW_TopoAF_afTop_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct Matrix
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (hO : OrthInv) (hB : TraceBase) (hN : TraceGramND) : VMod := by
  intro F E _ _ _ _ _ σ hCM M J hJ g μ hμ
  classical
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : FiniteDimensional F E := Lc.finite_nf F E
  obtain ⟨htr, ht2R, hlcR, hscR⟩ := Lc.tensor_adele_topology_holds F E
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M (AF F)
  set e : (Fin M → AF F ⊗[F] E) ≃ₗ[AF F] (Fin k → AF F) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := AF F) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) _
  let ec : (Fin M → AF F ⊗[F] E) ≃ₜ+ (Fin k → AF F) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → AF F) →ₗ[AF F] (Fin k → AF F) :=
    e.toLinearMap ∘ₗ ((lin (AF F) σ J g).restrictScalars (AF F)) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin (AF F) σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F (AF F))
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F (AF F) G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (hN F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, hB F E (AF F) σ M J]
    rfl
  have key : ∀ x y : Fin k → AF F, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → AF F, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := hO F k G X hGu hXG μ' hμ'
  have hlin : (lin (AF F) σ J g : (Fin M → AF F ⊗[F] E) → (Fin M → AF F ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → AF F ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]
end PI.VolSemiDirect.W.Cj
