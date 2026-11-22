-- Prove2me | solution 1 for OrderConvergesTo.sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:09.09287+00:00
-- url     : https://prove2.me/submissions/be14c92e-3864-4578-a221-c54c2d120faf

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
section
@[expose] public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
omit [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] in
private theorem isDirected_prod {κ τ : Type u} [Preorder κ] [Preorder τ]
    [IsDirected κ (· ≤ ·)] [IsDirected τ (· ≤ ·)] :
    IsDirected (κ × τ) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
  obtain ⟨l, hal, hbl⟩ := directed_of (· ≤ ·) a.2 b.2
  exact ⟨(k, l), ⟨hak, hal⟩, ⟨hbk, hbl⟩⟩
private theorem isGLB_range_add {κ τ : Type u} (r : κ → X) (s : τ → X)
    (hr : IsGLB (Set.range r) 0) (hs : IsGLB (Set.range s) 0) :
    IsGLB (Set.range (fun p : κ × τ => r p.1 + s p.2)) 0 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨k, l⟩, rfl⟩
    exact add_nonneg (hr.1 ⟨k, rfl⟩) (hs.1 ⟨l, rfl⟩)
  · intro w hw
    have hw_s : w ∈ lowerBounds (Set.range s) := by
      rintro _ ⟨l, rfl⟩
      have hw_r : w - s l ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hw ⟨(k, l), rfl⟩)
      exact sub_nonpos.mp (hr.2 hw_r)
    exact hs.2 hw_s
private theorem abs_sup_sub_sup_le_add (a b c d : X) :
    |(a ⊔ b) - (c ⊔ d)| ≤ |a - c| + |b - d| := by
  calc
    |(a ⊔ b) - (c ⊔ d)|
        = |((a ⊔ b) - (c ⊔ b)) + ((c ⊔ b) - (c ⊔ d))| := by
          congr 1
          abel
    _ ≤ |(a ⊔ b) - (c ⊔ b)| + |(c ⊔ b) - (c ⊔ d)| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      exact add_le_add (abs_sup_sub_sup_le_abs a c b) (by
        rw [sup_comm c b, sup_comm c d]
        exact abs_sup_sub_sup_le_abs b d c)
namespace OrderConvergesTo
end OrderConvergesTo
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
namespace OrderConvergesTo
theorem _root_.solution {ι : Type v} [Preorder ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i ⊔ v i) (x ⊔ y) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  rcases hv with ⟨τ, hτpre, hτdir, hτnon, s, hsanti, hsnn, hsglb, hsevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  let : Preorder τ := hτpre
  let : IsDirected τ (· ≤ ·) := hτdir
  let : Nonempty τ := hτnon
  let : IsDirected (κ × τ) (· ≤ ·) := isDirected_prod
  refine ⟨κ × τ, inferInstance, inferInstance, inferInstance,
    fun p => r p.1 + s p.2, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    exact add_le_add (hranti hpq.1) (hsanti hpq.2)
  · exact fun p => add_nonneg (hrnn p.1) (hsnn p.2)
  · exact isGLB_range_add r s hrglb hsglb
  · intro p
    exact ((hrevent p.1).and (hsevent p.2)).mono fun i hi => by
      exact (abs_sup_sub_sup_le_add (u i) (v i) x y).trans (add_le_add hi.1 hi.2)
end OrderConvergesTo
