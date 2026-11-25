-- Prove2me | solution 1 for PositivityTheory.ThKF.Unit.ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:39.012967+00:00
-- url     : https://prove2.me/submissions/c2ee805c-edae-4632-b0e3-db68a1b03734

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open PiTensorProduct
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
namespace PositivityTheory.ThKF.Unit
theorem _root_.solution (K : ∀ i, Submodule ℂ (V i)) (R : Submodule ℂ (⨂[ℂ] i, V i)) (hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R) :
    LinearMap.ker (map fun i => (K i).mkQ) ≤ R := by
  choose σ hσ using fun i => (K i).mkQ.exists_rightInverse_of_surjective (K i).range_mkQ
  have hd : ∀ i x, x - σ i ((K i).mkQ x) ∈ K i := fun i x => by
    rw [← Submodule.Quotient.mk_eq_zero]
    show (K i).mkQ _ = 0
    rw [map_sub, ← LinearMap.comp_apply (K i).mkQ (σ i), hσ, LinearMap.id_apply, sub_self]
  have h1 : ∀ (f : ∀ i, V i) (S : Finset ι), tprod ℂ f - tprod ℂ (fun i => if i ∈ S then σ i ((K i).mkQ (f i)) else f i) ∈ R := by
    intro f S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      let g : ∀ i, V i := fun i => if i ∈ S then σ i ((K i).mkQ (f i)) else f i
      have e1 : g = Function.update g j (f j) := by
        rw [eq_comm, Function.update_eq_self_iff]; simp [g, hj]
      have e2 : (fun i => if i ∈ insert j S then σ i ((K i).mkQ (f i)) else f i) = Function.update g j (σ j ((K j).mkQ (f j))) := by
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [g, h]
      have h3 := hR (Function.update g j (f j - σ j ((K j).mkQ (f j)))) j (by simpa using hd j (f j))
      rw [MultilinearMap.map_update_sub, ← e1, ← e2] at h3
      have h4 := R.add_mem (show tprod ℂ f - tprod ℂ g ∈ R from ih) h3
      rwa [sub_add_sub_cancel] at h4
  have h2 : ∀ x, x - map σ (map (fun i => (K i).mkQ) x) ∈ R := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul, map_smul, ← smul_sub, map_tprod, map_tprod]
      simpa using R.smul_mem c (h1 f Finset.univ)
    | add x y hx hy => rw [map_add, map_add, add_sub_add_comm]; exact R.add_mem hx hy
  intro x hx
  have := h2 x
  rwa [LinearMap.mem_ker.1 hx, map_zero, sub_zero] at this
end PositivityTheory.ThKF.Unit
