-- Prove2me | solution 1 for StrictTwoGroups.TwoEquiv.S_isTwoFunctor
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:20.137552+00:00
-- url     : https://prove2.me/submissions/0903ac0c-fbd9-4ca5-9d9b-14e6cdbc9526

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
theorem object_solution (G : StrictTwoGroups.TwoEquiv.StrictTwoGroup.{u})
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

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem S_map1_lawful {χ χ' : CrossedModule.{u}}
    (f : (χ.G → χ'.G) × (χ.H → χ'.H)) (hf : IsXModHom f) :
    IsTwoGrpHom (S.map1 f) := by
  let δ : χ.H →* χ'.H := MonoidHom.mk' f.2 hf.2.1
  refine ⟨hf.1,?_,?_,?_,?_⟩
  · intro x y
    apply SemidirectProduct.ext
    · change f.2 (x.left*χ.α x.right y.left)=f.2 x.left*χ'.α (f.1 x.right) (f.2 y.left)
      rw [hf.2.1,hf.2.2.2]
    · exact hf.1 _ _
  · intro x
    constructor
    · rfl
    · change χ'.τ (f.2 x.left)*f.1 x.right=f.1 (χ.τ x.left*x.right)
      rw [hf.2.2.1,hf.1]
  · intro g
    apply SemidirectProduct.ext
    · exact δ.map_one
    · rfl
  · intro a b hab
    apply SemidirectProduct.ext
    · exact hf.2.1 _ _
    · rfl

theorem crossed_naturality {χ χ' : CrossedModule.{u}} (hχ' : IsCrossedModule χ')
    (f g : (χ.G → χ'.G) × (χ.H → χ'.H)) (hf : IsXModHom f)
    (η : χ.G → χ'.H) (hη : IsXModTwoHom f g η) (h : χ.H) (x : χ.G) :
    η (χ.τ h*x)*f.2 h=g.2 h*η x := by
  rw [hη.1,hη.2.2,←hf.2.2.1,hχ']
  group

theorem S_map2_lawful {χ χ' : CrossedModule.{u}} (hχ' : IsCrossedModule χ')
    (f g : (χ.G → χ'.G) × (χ.H → χ'.H)) (hf : IsXModHom f)
    (η : χ.G → χ'.H) (hη : IsXModTwoHom f g η) :
    IsTwoGrpTwoHom (S.map1 f) (S.map1 g) (S.map2 f g η) := by
  refine ⟨?_,?_,?_⟩
  · intro x y
    apply SemidirectProduct.ext
    · exact hη.1 _ _
    · exact hf.1 _ _
  · intro x
    change χ.G at x
    constructor
    · rfl
    · change χ'.τ (η x)*f.1 x=g.1 x
      rw [hη.2.1]
      group
  · intro a
    apply SemidirectProduct.ext
    · exact crossed_naturality hχ' f g hf η hη a.left a.right
    · rfl

theorem crossed_horizontal_identity {χ χ' χ'' : CrossedModule.{u}} (hχ'' : IsCrossedModule χ'')
    (f g : (χ.G → χ'.G) × (χ.H → χ'.H))
    (f' g' : (χ'.G → χ''.G) × (χ'.H → χ''.H)) (hf' : IsXModHom f')
    (η : χ.G → χ'.H) (η' : χ'.G → χ''.H)
    (hη : IsXModTwoHom f g η) (hη' : IsXModTwoHom f' g' η') (x : χ.G) :
    g'.2 (η x)*η' (f.1 x)=η' (g.1 x)*f'.2 (η x) := by
  have he : χ'.τ (η x)*f.1 x=g.1 x := by rw [hη.2.1]; group
  have h := crossed_naturality hχ'' f' g' hf' η' hη' (η x) (f.1 x)
  rw [he] at h
  exact h.symm
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem S_isTwoFunctor : IsTwoFunctor S.{u} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact toTwoGrp_isStrictTwoGroup
  · intro χ χ' f hχ hχ' hf
    exact S_map1_lawful f hf
  · intro χ χ' f g η hχ hχ' hf hg hη
    exact S_map2_lawful hχ' f g hf η hη
  · intro χ χ' f hχ hχ' hf
    rfl
  · intro χ χ' f g h η φ hχ hχ' hf hg hh hη hφ
    rfl
  · intro χ χ' χ'' f g hχ hχ' hχ'' hf hg
    rfl
  · intro χ χ' χ'' f g f' g' η η' hχ hχ' hχ'' hf hg hf' hg' hη hη'
    funext x
    apply SemidirectProduct.ext
    · exact crossed_horizontal_identity hχ'' f g f' g' hf' η η' hη hη' x
    · rfl
  · intro χ hχ
    rfl
  · intro χ hχ
    rfl
end StrictTwoGroups.TwoEquiv
universe u
theorem solution : StrictTwoGroups.TwoEquiv.IsTwoFunctor StrictTwoGroups.TwoEquiv.S.{u} :=
  StrictTwoGroups.TwoEquiv.S_isTwoFunctor

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem kerProj_identity (G : StrictTwoGroup.{u}) (g : G.G0) : kerProj G (G.i g)=1 := by
  apply Subtype.ext
  simp [kerProj,G.s_i]

theorem kerProj_multiply (G : StrictTwoGroup.{u}) (a b : G.G1) :
    kerProj G (a*b)=kerProj G a * (MulAut.conjNormal.comp G.i) (G.s a) (kerProj G b) := by
  apply Subtype.ext
  simp only [kerProj,toXMod,Subgroup.coe_mul,MonoidHom.comp_apply,MulAut.conjNormal_apply,
    map_mul,mul_inv_rev]
  group

theorem kerProj_composite (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (hab : G.s a=G.t b) :
    kerProj G (G.comp a b)=kerProj G a*kerProj G b := by
  apply Subtype.ext
  change G.comp a b*(G.i (G.s (G.comp a b)))⁻¹=
    (a*(G.i (G.s a))⁻¹)*(b*(G.i (G.s b))⁻¹)
  rw [(hG.1 a b hab).1,proposition_comp_formula G hG a b hab]
  group

theorem T_map1_coe {G G' : StrictTwoGroup.{u}}
    (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) (h : ↥G.s.ker) :
    ((kerProj G' (F.2 h)) : G'.G1)=F.2 h := by
  let F0 : G.G0 →* G'.G0 := MonoidHom.mk' F.1 hF.1
  have hs : G'.s (F.2 h)=1 := by rw [(hF.2.2.1 h).1,h.property]; exact F0.map_one
  change F.2 h*(G'.i (G'.s (F.2 h)))⁻¹=F.2 h
  simp [hs]

theorem kerProj_map {G G' : StrictTwoGroup.{u}}
    (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) (a : G.G1) :
    kerProj G' (F.2 a)=(T.map1 F).2 (kerProj G a) := by
  let F1 : G.G1 →* G'.G1 := MonoidHom.mk' F.2 hF.2.1
  apply Subtype.ext
  change (kerProj G' (F.2 a):G'.G1)=(kerProj G' (F.2 (kerProj G a)):G'.G1)
  rw [T_map1_coe F hF]
  change F.2 a*(G'.i (G'.s (F.2 a)))⁻¹=F1 (a*(G.i (G.s a))⁻¹)
  rw [map_mul,map_inv,(hF.2.2.1 a).1]
  change F.2 a*(G'.i (F.1 (G.s a)))⁻¹=F.2 a*(F.2 (G.i (G.s a)))⁻¹
  rw [hF.2.2.2.1]

theorem T_map1_lawful {G G' : StrictTwoGroup.{u}}
    (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) :
    IsXModHom (T.map1 F) := by
  change (∀ x y : G.G0, F.1 (x*y)=F.1 x*F.1 y) ∧
    (∀ h k : ↥G.s.ker,kerProj G' (F.2 (h*k))=kerProj G' (F.2 h)*kerProj G' (F.2 k)) ∧
    (∀ h : ↥G.s.ker,G'.t (kerProj G' (F.2 h):G'.G1)=F.1 (G.t h)) ∧
    (∀ (g : G.G0) (h : ↥G.s.ker),
      kerProj G' (F.2 ((MulAut.conjNormal.comp G.i) g h))=
        (MulAut.conjNormal.comp G'.i) (F.1 g) (kerProj G' (F.2 h)))
  let F1 : G.G1 →* G'.G1 := MonoidHom.mk' F.2 hF.2.1
  refine ⟨hF.1,?_,?_,?_⟩
  · intro h k
    apply Subtype.ext
    calc
      _ = F.2 ((h:G.G1)*(k:G.G1)) := T_map1_coe F hF (h*k)
      _ = F.2 h*F.2 k := hF.2.1 _ _
      _ = _ := congrArg₂ (fun a b : G'.G1 => a*b) (T_map1_coe F hF h).symm (T_map1_coe F hF k).symm
  · intro h
    change G'.t (kerProj G' (F.2 h):G'.G1)=F.1 (G.t h)
    rw [T_map1_coe F hF]
    exact (hF.2.2.1 h).2
  · intro g h
    apply Subtype.ext
    change (kerProj G' (F.2 ((MulAut.conjNormal.comp G.i) g h)):G'.G1)=
      ((MulAut.conjNormal.comp G'.i) (F.1 g) (kerProj G' (F.2 h)):G'.G1)
    rw [T_map1_coe F hF]
    change F1 (G.i g*(h:G.G1)*(G.i g)⁻¹)=
      G'.i (F.1 g)*(kerProj G' (F.2 h):G'.G1)*(G'.i (F.1 g))⁻¹
    rw [map_mul,map_mul,map_inv,T_map1_coe F hF]
    change F.2 (G.i g)*F.2 h*(F.2 (G.i g))⁻¹=_
    rw [hF.2.2.2.1]
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem T_map2_lawful {G G' : StrictTwoGroup.{u}} (hG' : IsStrictTwoGroup G')
    (F E : (G.G0 → G'.G0) × (G.G1 → G'.G1)) (hF : IsTwoGrpHom F) (hE : IsTwoGrpHom E)
    (θ : G.G0 → G'.G1) (hθ : IsTwoGrpTwoHom F E θ) :
    IsXModTwoHom (T.map1 F) (T.map1 E) (T.map2 F E θ) := by
  change (∀ x y : G.G0,kerProj G' (θ (x*y))=
    kerProj G' (θ x)*(MulAut.conjNormal.comp G'.i) (F.1 x) (kerProj G' (θ y))) ∧
    (∀ x : G.G0,G'.t (kerProj G' (θ x):G'.G1)=E.1 x*(F.1 x)⁻¹) ∧
    (∀ h : ↥G.s.ker,kerProj G' (θ (G.t h))=kerProj G' (E.2 h)*(kerProj G' (F.2 h))⁻¹)
  refine ⟨?_,?_,?_⟩
  · intro x y
    change kerProj G' (θ (x*y))=kerProj G' (θ x)*(MulAut.conjNormal.comp G'.i) (F.1 x) (kerProj G' (θ y))
    rw [hθ.1,kerProj_multiply,(hθ.2.1 x).1]
  · intro x
    change G.G0 at x
    change G'.t (θ x*(G'.i (G'.s (θ x)))⁻¹)=E.1 x*(F.1 x)⁻¹
    rw [map_mul,map_inv,G'.t_i,(hθ.2.1 x).1,(hθ.2.1 x).2]
  · intro h
    change ↥G.s.ker at h
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,T_map1_coe F hF,T_map1_coe E hE]
    let θhom : G.G0 →* G'.G1 := MonoidHom.mk' θ hθ.1
    let E0 : G.G0 →* G'.G0 := MonoidHom.mk' E.1 hE.1
    have hθ1 : θ 1=1 := θhom.map_one
    have hEs : G'.s (E.2 h)=1 := by rw [(hE.2.2.1 h).1,h.property]; exact E0.map_one
    have hu : G'.comp (E.2 h) 1=E.2 h := by simpa [hEs] using (hG'.2.1 (E.2 h)).1
    have hn := hθ.2.2 (h:G.G1)
    rw [h.property,hθ1,hu] at hn
    have hc : G'.s (θ (G.t h))=G'.t (F.2 h) := (hθ.2.1 _).1.trans (hF.2.2.1 h).2.symm
    rw [proposition_comp_formula G' hG' _ _ hc] at hn
    exact (eq_mul_inv_iff_mul_eq).mpr hn
end StrictTwoGroups.TwoEquiv

end

section
namespace StrictTwoGroups.TwoEquiv
universe u

theorem T_isTwoFunctor : IsTwoFunctor T.{u} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact toXMod_isCrossedModule
  · intro G G' F hG hG' hF
    exact T_map1_lawful F hF
  · intro G G' F E θ hG hG' hF hE hθ
    exact T_map2_lawful hG' F E hF hE θ hθ
  · intro G G' F hG hG' hF
    funext x
    exact kerProj_identity G' (F.1 x)
  · intro G G' F E K θ φ hG hG' hF hE hK hθ hφ
    funext x
    exact kerProj_composite G' hG' (φ x) (θ x) ((hφ.2.1 x).1.trans (hθ.2.1 x).2.symm)
  · intro G G' G'' F E hG hG' hG'' hF hE
    change StrictTwoGroup.{u} at G G' G''
    apply Prod.ext
    · rfl
    · funext h
      change ↥G.s.ker at h
      exact kerProj_map E hE (F.2 h)
  · intro G G' G'' F E F' E' θ θ' hG hG' hG'' hF hE hF' hE' hθ hθ'
    change StrictTwoGroup.{u} at G G' G''
    funext x
    change G.G0 at x
    have hn := hθ'.2.2 (θ x)
    rw [(hθ.2.1 x).1,(hθ.2.1 x).2] at hn
    change kerProj G'' (G''.comp (θ' (E.1 x)) (F'.2 (θ x)))=
      kerProj G'' (E'.2 (kerProj G' (θ x)))*kerProj G'' (θ' (F.1 x))
    rw [hn]
    have hc : G''.s (E'.2 (θ x))=G''.t (θ' (F.1 x)) := by
      rw [(hE'.2.2.1 (θ x)).1,(hθ.2.1 x).1,(hθ'.2.1 (F.1 x)).2]
    rw [kerProj_composite G'' hG'' _ _ hc,kerProj_map E' hE']
    rfl
  · intro G hG
    change StrictTwoGroup.{u} at G
    apply Prod.ext
    · rfl
    · funext h
      change ↥G.s.ker at h
      apply Subtype.ext
      change (h:G.G1)*(G.i (G.s h))⁻¹=(h:G.G1)
      have hh : G.s (h:G.G1)=1 := h.property
      rw [hh]
      simp
  · intro G hG
    funext x
    exact kerProj_identity G x
end StrictTwoGroups.TwoEquiv

end

section
namespace Queelius.StrictTwoGroups.Controls
open StrictTwoGroups.TwoEquiv

/-- In a lawful pair groupoid, the kernel coordinate is a cocycle, not a group morphism. -/
theorem kernel_projection_not_multiplicative :
    let G := pairGroupoid (Equiv.Perm (Fin 3))
    let a : G.G1 := (1,q)
    let b : G.G1 := (p,1)
    kerProj G (a*b) ≠ kerProj G a*kerProj G b := by
  dsimp only
  intro h
  have hh := congrArg (fun k : ↥(pairGroupoid (Equiv.Perm (Fin 3))).s.ker => k.val.1) h
  change p*q⁻¹=q⁻¹*p at hh
  have hn : (p*q⁻¹ : Equiv.Perm (Fin 3)) ≠ q⁻¹*p := by decide
  exact hn hh

/-- Multiplication of already-kernel arrows needs no twisting. -/
theorem kernel_projection_on_kernel (G : StrictTwoGroup) (h : ↥G.s.ker) :
    kerProj G h=h := by
  apply Subtype.ext
  have hh : G.s (h:G.G1)=1 := h.property
  change (h:G.G1)*(G.i (G.s h))⁻¹=(h:G.G1)
  rw [hh]
  simp
end Queelius.StrictTwoGroups.Controls

end
