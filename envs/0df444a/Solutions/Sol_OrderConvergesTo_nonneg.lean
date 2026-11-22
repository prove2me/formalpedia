-- Prove2me | solution 1 for OrderConvergesTo.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:10.933821+00:00
-- url     : https://prove2.me/submissions/c943df8c-384f-4cdf-9c84-c763f592d962

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
namespace OrderConvergesTo
theorem _root_.solution {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) (hnn : ∀ i, 0 ≤ u i) :
    0 ≤ x := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, _hranti, _hrnn, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  have hlb : -x ∈ lowerBounds (Set.range r) := by
    rintro _ ⟨k, rfl⟩
    rcases (hrevent k).exists with ⟨i, hi⟩
    have hx_le : -x ≤ u i - x := by
      simpa [zero_sub] using sub_le_sub_right (hnn i) x
    exact hx_le.trans ((le_abs_self (u i - x)).trans hi)
  exact neg_nonpos.mp (hrglb.2 hlb)
end OrderConvergesTo
