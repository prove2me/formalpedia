-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_lifts_eventually_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:50:52.469963+00:00
-- url     : https://prove2.me/submissions/2269b7c4-4c76-49dc-aac0-c3b069500417

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    {X : Type*} [TopologicalSpace X] (u v : X→ℍ) (x : X)
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (he : (fun z => Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (v z)) =ᶠ[𝓝 x]
      (fun z => Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (u z))) :
    ∃ γ : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      v =ᶠ[𝓝 x] (fun z => γ.val • u z) := by
  have h0 := Quotient.eq''.mp he.eq_of_nhds
  obtain ⟨γ,hγ⟩ := h0
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt (v x)
  have he0 : v x∈e.target := hf.self_mem_localInverseAt_target
  have hvo : ∀ᶠ z in 𝓝 x, v z∈e.target := hv (e.open_target.mem_nhds he0)
  have hgo : ∀ᶠ z in 𝓝 x, γ.val • u z∈e.target := by
    apply ((continuous_const_smul γ.val).continuousAt.comp hu)
    change e.target∈𝓝 (γ.val • u x)
    change γ.val • u x=v x at hγ
    rw [hγ]
    exact e.open_target.mem_nhds he0
  refine ⟨γ,?_⟩
  filter_upwards [hvo,hgo,he] with z hvz hgz hez
  apply hf.injOn_localInverseAt_target hvz hgz
  calc
    Quotient.mk _ (v z)=Quotient.mk _ (u z) := hez
    _=Quotient.mk _ (γ.val • u z) := by
      apply Quotient.sound
      exact ⟨γ⁻¹,by
        change γ⁻¹ • (γ • u z)=u z
        exact inv_smul_smul γ (u z)⟩
end QEC.Coding.TannerLiftedProduct
