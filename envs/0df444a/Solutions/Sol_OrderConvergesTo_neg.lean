-- Prove2me | solution 1 for OrderConvergesTo.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:20.953805+00:00
-- url     : https://prove2.me/submissions/1006c4f8-0cdd-455b-9dc9-0900bd099438

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
omit [IsOrderedAddMonoid X]
namespace OrderConvergesTo
theorem _root_.solution {ι : Type v} [Preorder ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => -u i) (-x) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnn, hrglb, ?_⟩
  intro k
  exact (hrevent k).mono fun i hi => by
    calc
      |-u i - -x| = |-(u i - x)| := by
        congr 1
        abel
      _ = |u i - x| := abs_neg _
      _ ≤ r k := hi
end OrderConvergesTo
