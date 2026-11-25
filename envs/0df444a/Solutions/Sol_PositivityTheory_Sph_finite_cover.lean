-- Prove2me | solution 1 for PositivityTheory.Sph.finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:05.040264+00:00
-- url     : https://prove2.me/submissions/82f28f70-8976-45a4-a6b9-45c6097e56b9

import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_ExistsVBallSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PositivityTheory.Sph
open ValuativeRel Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private lemma isOpen_vle (r : k) (hr : r ≠ 0) : IsOpen {x : k | valuation k x ≤ valuation k r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 (valuation k r) (by simpa using hr), fun z hz => ?_⟩
  have h : z = (z - x) + x := by ring
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hx ⊢
  rw [h]
  exact (Valuation.map_add _ _ _).trans (max_le hz.le hx)
private lemma vBall_eq {m p : Type} (r : k) : (vBall r : Set (Matrix m p k)) =
    Set.pi Set.univ (fun _ : m => Set.pi Set.univ
      (fun _ : p => {x : k | valuation k x ≤ valuation k r})) := by
  ext Z
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
private lemma isOpen_vBall {m p : Type} [Finite m] [Finite p] (r : k) (hr : r ≠ 0) :
    IsOpen (vBall r : Set (Matrix m p k)) := by
  rw [vBall_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_vle r hr
private lemma isCompact_vBall {m p : Type} (r : k) : IsCompact (vBall r : Set (Matrix m p k)) := by
  rw [vBall_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall k _
private lemma zero_mem_vBall {m p : Type} (r : k) : (0 : Matrix m p k) ∈ vBall r := by
  intro i j; simp
end PositivityTheory.Sph
end
end

set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph
open ValuativeRel Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.Sph
theorem _root_.solution {m p : Type} [Fintype m] [Fintype p] (t : k) (ht : t ≠ 0) :
    ∃ S : Finset (Matrix m p k), ∀ Y, IntM (t • Y) → ∃ y ∈ S, ∃ Z, IntM Z ∧ Y = y + t • Z := by
  classical
  have hc : IsCompact (vBall (m := m) (p := p) t⁻¹) := isCompact_vBall _
  obtain ⟨S, -, hS⟩ := hc.elim_nhds_subcover (fun x => (fun Y => Y - x) ⁻¹' vBall t)
    (fun x _ => IsOpen.mem_nhds
      ((isOpen_vBall _ ht).preimage (continuous_id.sub continuous_const))
      (by simpa using zero_mem_vBall (m := m) (p := p) t))
  refine ⟨S, fun Y hY => ?_⟩
  have hYb : Y ∈ vBall t⁻¹ := by
    intro i j
    have h := (Valuation.mem_integer_iff _ _).1 (hY i j)
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [show Y i j = t⁻¹ * (t * Y i j) from (inv_mul_cancel_left₀ ht _).symm, map_mul]
    exact mul_le_of_le_one_right' h
  obtain ⟨y, hyS, hy⟩ := Set.mem_iUnion₂.1 (hS hYb)
  refine ⟨y, hyS, t⁻¹ • (Y - y), fun i j => ?_, ?_⟩
  · have h := hy i j
    rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    calc (valuation k t)⁻¹ * valuation k ((Y - y) i j) ≤ (valuation k t)⁻¹ * valuation k t :=
          mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ (by simpa using ht)
  · rw [smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]
end PositivityTheory.Sph
