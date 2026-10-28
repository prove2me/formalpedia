-- Prove2me | solution 1 for StrictTwoGroups.TwoEquiv.toXMod_isCrossedModule
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:47.988527+00:00
-- url     : https://prove2.me/submissions/9dd7ddf4-2792-434a-ac51-7d2e25f48c45

import Definitions.Def_StrictTwoGroups_TwoEquiv_CrossedModule
import Definitions.Def_StrictTwoGroups_TwoEquiv_Raw2Cat
import Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup
import Definitions.Def_StrictTwoGroups_TwoEquiv_XMod
import Definitions.Def_StrictTwoGroups_TwoEquiv_TwoGrp
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors
import Init
import Mathlib






section
set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv
universe u

/-- Units and interchange already determine composition on composable pairs. -/
theorem composition_from_units_interchange (G : StrictTwoGroup.{u})
    (hunit : ∀ a, G.comp a (G.i (G.s a)) = a ∧ G.comp (G.i (G.t a)) a = a)
    (hinter : ∀ a b a' b', G.s a = G.t b → G.s a' = G.t b' →
      G.comp (a * a') (b * b') = G.comp a b * G.comp a' b')
    (a b : G.G1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b := by
  let y := (G.i (G.s a))⁻¹ * b
  have hty : G.t y = 1 := by
    simp [y, map_mul, map_inv, G.t_i, hab]
  have hleft : G.comp 1 y = y := by
    simpa [hty] using (hunit y).2
  have h := hinter a (G.i (G.s a)) 1 y (by rw [G.t_i]) (by simp [hty])
  simpa [y, mul_assoc, (hunit a).1, hleft] using h

theorem proposition_comp_formula (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b :=
  composition_from_units_interchange G hG.2.1 hG.2.2.2 a b hab

theorem corollary_comp_ker (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (ha : G.s a = 1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b ∧ G.comp a b = a * b := by
  have h := proposition_comp_formula G hG a b hab
  exact ⟨h, by simpa [ha] using h⟩

end StrictTwoGroups.TwoEquiv

universe u
theorem composition_solution (G : StrictTwoGroups.TwoEquiv.StrictTwoGroup.{u})
    (hG : StrictTwoGroups.TwoEquiv.IsStrictTwoGroup G) (a b : G.G1)
    (hab : G.s a = G.t b) : G.comp a b = a * (G.i (G.s a))⁻¹ * b :=
  StrictTwoGroups.TwoEquiv.proposition_comp_formula G hG a b hab

end


section
set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv
universe u

theorem source_kernel_part (G : StrictTwoGroup.{u}) (a : G.G1) :
    a * (G.i (G.s a))⁻¹ ∈ G.s.ker := by
  simp [MonoidHom.mem_ker, G.s_i]

/-- The source retraction splits the arrow group; category axioms are unnecessary. -/
def sourceSplit (G : StrictTwoGroup.{u}) :
    G.G1 ≃* (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) where
  toFun a := ⟨⟨a * (G.i (G.s a))⁻¹, source_kernel_part G a⟩, G.s a⟩
  invFun x := (x.left : G.G1) * G.i x.right
  left_inv a := by simp [mul_assoc]
  right_inv x := by
    have hx : G.s (x.left : G.G1) = 1 := x.left.property
    apply SemidirectProduct.ext
    · apply Subtype.ext
      simp only [map_mul, G.s_i, hx, one_mul]
      simp [mul_assoc]
    · simp only [map_mul, G.s_i, hx, one_mul]
  map_mul' a b := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      simp only [SemidirectProduct.mul_left, Subgroup.coe_mul,
        MonoidHom.comp_apply, MulAut.conjNormal_apply, map_mul, mul_inv_rev]
      group
    · exact map_mul G.s a b

theorem sourceSplit_left (G : StrictTwoGroup.{u}) (a : G.G1) :
    ((sourceSplit G a).left : G.G1) = a * (G.i (G.s a))⁻¹ := rfl

theorem sourceSplit_right (G : StrictTwoGroup.{u}) (a : G.G1) :
    (sourceSplit G a).right = G.s a := rfl

theorem sourceSplit_symm (G : StrictTwoGroup.{u})
    (x : ↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0) :
    (sourceSplit G).symm x = (x.left : G.G1) * G.i x.right := rfl

theorem phi_mulEquiv (G : StrictTwoGroup.{u}) :
    ∃ e : G.G1 ≃* (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0),
      (∀ a, ((e a).left : G.G1) = a * (G.i (G.s a))⁻¹ ∧ (e a).right = G.s a) ∧
      ∀ x, e.symm x = (x.left : G.G1) * G.i x.right := by
  exact ⟨sourceSplit G, fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

end StrictTwoGroups.TwoEquiv

end

section
set_option autoImplicit false

namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv
universe u

/-- A strict two-group whose arrow group is noncommutative when `H` is. -/
def pairGroupoid (H : Type u) [Group H] : StrictTwoGroup.{u} where
  G0 := H
  G1 := H × H
  s := MonoidHom.snd H H
  t := MonoidHom.fst H H
  i := (MonoidHom.id H).prod (MonoidHom.id H)
  comp a b := (a.1, b.2)
  s_i _ := rfl
  t_i _ := rfl

theorem pairGroupoid_strict (H : Type u) [Group H] :
    IsStrictTwoGroup (pairGroupoid H) := by
  constructor
  · intro a b _
    exact ⟨rfl, rfl⟩
  constructor
  · intro a
    exact ⟨rfl, rfl⟩
  constructor
  · intro a b c _ _
    rfl
  · intro a b a' b' _ _
    rfl

abbrev p : Equiv.Perm (Fin 3) := Equiv.swap 0 1
abbrev q : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem permutations_do_not_commute : p * q ≠ q * p := by decide

/-- Reversing the factor order in the kernel coordinate changes the result. -/
theorem reversed_kernel_coordinate_fails :
    let G := pairGroupoid (Equiv.Perm (Fin 3))
    let a : G.G1 := (p, q)
    a * (G.i (G.s a))⁻¹ ≠ (G.i (G.s a))⁻¹ * a := by
  change ((p, q) * (q, q)⁻¹ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ≠
    (q, q)⁻¹ * (p, q)
  decide

/-- The formula is only asserted for composable arrows. -/
theorem noncomposable_formula_fails :
    let G := pairGroupoid (Equiv.Perm (Fin 3))
    let a : G.G1 := (1, 1)
    let b : G.G1 := (p, 1)
    G.s a ≠ G.t b ∧ G.comp a b ≠ a * (G.i (G.s a))⁻¹ * b := by
  change (1 : Equiv.Perm (Fin 3)) ≠ p ∧
    ((1, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ≠
      ((1, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) *
      ((1, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))⁻¹ *
      ((p, 1) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  decide

end Queelius.StrictTwoGroups.Controls

end

section
set_option autoImplicit false
namespace StrictTwoGroups.TwoEquiv
universe u

theorem source_target_kernel_commute (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (ha : G.s a = 1) (hb : G.t b = 1) : a * b = b * a := by
  have h1b : G.comp 1 b = b := by simpa [hb] using (hG.2.1 b).2
  have ha1 : G.comp a 1 = a := by simpa [ha] using (hG.2.1 a).1
  have hi := hG.2.2.2 1 b a 1 (by simp [hb]) (by simp [ha])
  calc
    a*b = G.comp a b := ((corollary_comp_ker G hG a b ha (ha.trans hb.symm)).2).symm
    _ = b*a := by simpa [h1b,ha1] using hi

theorem source_kernel_peiffer (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (h h' : ↥G.s.ker) :
    G.i (G.t h) * (h' : G.G1) * (G.i (G.t h))⁻¹ = (h : G.G1) * h' * (h : G.G1)⁻¹ := by
  let z := (G.i (G.t h))⁻¹ * (h : G.G1)
  have hz : G.t z = 1 := by simp [z, G.t_i]
  have hc := source_target_kernel_commute G hG (h' : G.G1) z h'.property hz
  calc
    _ = G.i (G.t h) * ((h' : G.G1)*z) * (h : G.G1)⁻¹ := by dsimp [z]; group
    _ = G.i (G.t h) * (z*(h' : G.G1)) * (h : G.G1)⁻¹ := by rw [hc]
    _ = _ := by dsimp [z]; group

theorem toXMod_isCrossedModule (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G) :
    IsCrossedModule (toXMod G) := by
  intro h h'
  apply Subtype.ext
  exact source_kernel_peiffer G hG h h'

end StrictTwoGroups.TwoEquiv
universe u
theorem solution (G : StrictTwoGroups.TwoEquiv.StrictTwoGroup.{u})
    (hG : StrictTwoGroups.TwoEquiv.IsStrictTwoGroup G) :
    StrictTwoGroups.TwoEquiv.IsCrossedModule (StrictTwoGroups.TwoEquiv.toXMod G) :=
  StrictTwoGroups.TwoEquiv.toXMod_isCrossedModule G hG

end

section
set_option autoImplicit false
namespace StrictTwoGroups.TwoEquiv
universe u

theorem toTwoGrp_isStrictTwoGroup (χ : CrossedModule.{u}) (hχ : IsCrossedModule χ) :
    IsStrictTwoGroup (toTwoGrp χ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b hab
    change a.right = χ.τ b.left * b.right at hab
    constructor
    · rfl
    · change χ.τ (a.left*b.left)*b.right = χ.τ a.left*a.right
      rw [map_mul,hab,mul_assoc]
  · intro a
    constructor
    · apply SemidirectProduct.ext
      · change a.left*1=a.left
        exact mul_one _
      · rfl
    · apply SemidirectProduct.ext
      · change 1*a.left=a.left
        exact one_mul _
      · rfl
  · intro a b c hab hbc
    apply SemidirectProduct.ext
    · exact mul_assoc _ _ _
    · rfl
  · intro a b a' b' hab hab'
    change a.right = χ.τ b.left * b.right at hab
    apply SemidirectProduct.ext
    · change (a.left * χ.α a.right a'.left) * (b.left * χ.α b.right b'.left) =
        (a.left*b.left)*χ.α b.right (a'.left*b'.left)
      rw [hab, map_mul, MulAut.mul_apply, hχ, map_mul]
      group
    · rfl

end StrictTwoGroups.TwoEquiv

end

section
set_option autoImplicit false
namespace StrictTwoGroups.TwoEquiv
universe u

theorem peiffer_of_toTwoGrp_strict (χ : CrossedModule.{u})
    (hG : IsStrictTwoGroup (toTwoGrp χ)) : IsCrossedModule χ := by
  intro h h'
  let a : χ.H ⋊[χ.α] χ.G := ⟨1,χ.τ h⟩
  let b : χ.H ⋊[χ.α] χ.G := ⟨h,1⟩
  let a' : χ.H ⋊[χ.α] χ.G := ⟨h',1⟩
  have hi := hG.2.2.2 a b a' 1
    (by change χ.τ h = χ.τ h*1; simp)
    (by change (1:χ.G) = χ.τ 1*1; simp)
  have hl := congrArg SemidirectProduct.left hi
  change (1*χ.α (χ.τ h) h')*(h*χ.α 1 1) = (1*h)*χ.α 1 (h'*1) at hl
  have he : χ.α (χ.τ h) h' * h = h*h' := by
    simpa using hl
  exact (eq_mul_inv_iff_mul_eq).mpr he

theorem toTwoGrp_strict_iff (χ : CrossedModule.{u}) :
    IsStrictTwoGroup (toTwoGrp χ) ↔ IsCrossedModule χ :=
  ⟨peiffer_of_toTwoGrp_strict χ,toTwoGrp_isStrictTwoGroup χ⟩

end StrictTwoGroups.TwoEquiv
namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv
universe u

/-- Equivariant boundary data with trivial object group need not satisfy Peiffer. -/
def trivialBoundary (H : Type u) [Group H] : CrossedModule.{u} where
  G := PUnit
  H := H
  τ := 1
  α := 1
  equivariant _ _ := by simp

theorem trivialBoundary_peiffer_iff (H : Type u) [Group H] :
    IsCrossedModule (trivialBoundary H) ↔ ∀ a b : H, a*b=b*a := by
  constructor
  · intro h a b
    have he := h a b
    change b=a*b*a⁻¹ at he
    exact ((eq_mul_inv_iff_mul_eq).mp he).symm
  · intro hc a b
    change b=a*b*a⁻¹
    apply (eq_mul_inv_iff_mul_eq).mpr
    exact (hc a b).symm

theorem nonabelian_trivial_boundary_not_crossed :
    ¬ IsCrossedModule (trivialBoundary (Equiv.Perm (Fin 3))) := by
  intro h
  exact permutations_do_not_commute ((trivialBoundary_peiffer_iff _).mp h p q)

theorem equivariance_alone_does_not_give_strict_group :
    ¬ IsStrictTwoGroup (toTwoGrp (trivialBoundary (Equiv.Perm (Fin 3)))) :=
  fun h => nonabelian_trivial_boundary_not_crossed (peiffer_of_toTwoGrp_strict _ h)

theorem abelian_trivial_boundary_is_strict (H : Type u) [CommGroup H] :
    IsStrictTwoGroup (toTwoGrp (trivialBoundary H)) :=
  toTwoGrp_isStrictTwoGroup _ ((trivialBoundary_peiffer_iff H).mpr (fun _ _ => mul_comm _ _))

end Queelius.StrictTwoGroups.Controls

end
