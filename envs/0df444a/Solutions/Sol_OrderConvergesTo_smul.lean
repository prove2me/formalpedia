-- Prove2me | solution 1 for OrderConvergesTo.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:44.159005+00:00
-- url     : https://prove2.me/submissions/10f812fb-3cc0-4514-8176-41c82a604fd4

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Theorems.Thm_P2M_abs_smul__56c684b926d9
public import Theorems.Thm_isGLB_smul_of_nonneg


set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
namespace OrderConvergesTo
theorem _root_.solution [VectorLattice X] (a : ℝ) {ι : Type v} [Preorder ι]
      {u : ι → X} {x : X}
    (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => a • u i) (a • x) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, fun k => |a| • r k, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact smul_le_smul_of_nonneg_left (hranti hkl) (abs_nonneg a)
  · exact fun k => smul_nonneg (abs_nonneg a) (hrnn k)
  · have h := isGLB_smul_of_nonneg (X := X) (lam := |a|) (abs_nonneg a) hrglb
    have hset :
        Set.range (fun k => |a| • r k) = (fun z => |a| • z) '' Set.range r := by
      ext z
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨r k, ⟨k, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
    simpa [hset] using h
  · intro k
    exact (hrevent k).mono fun i hi => by
      calc
        |a • u i - a • x| = |a • (u i - x)| := by
          rw [smul_sub]
        _ = |a| • |u i - x| := abs_smul' (X := X) (x := u i - x) a
        _ ≤ |a| • r k := smul_le_smul_of_nonneg_left hi (abs_nonneg a)
end OrderConvergesTo
