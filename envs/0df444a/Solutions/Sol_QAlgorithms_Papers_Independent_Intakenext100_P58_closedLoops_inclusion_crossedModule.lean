-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P58.closedLoops_inclusion_crossedModule
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T11:13:27.435047+00:00
-- url     : https://prove2.me/submissions/85e9c295-aab4-4d26-acd6-3b4269217242

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P58

namespace QAlgorithms.Papers.Independent.Intakenext100.P58.S09Algebra

universe u v
variable {M : Type u} {A : Type v} (D : GroupoidData M A)

/-- Cancel an arrow after multiplying on the left by its inverse. -/
theorem inv_mul_cancel_left (a b : A) (h : D.s a = D.t b) :
    D.mul (D.inv a) (D.mul a b) = b := by
  calc
    D.mul (D.inv a) (D.mul a b) = D.mul (D.mul (D.inv a) a) b :=
      (D.assoc _ _ _ (D.s_inv a) h).symm
    _ = D.mul (D.unit (D.s a)) b := by rw [D.inv_left]
    _ = b := by rw [h, D.unit_left]

/-- Cancel an inverse after multiplying on the left by its arrow. -/
theorem mul_inv_cancel_left (a b : A) (h : D.t a = D.t b) :
    D.mul a (D.mul (D.inv a) b) = b := by
  calc
    D.mul a (D.mul (D.inv a) b) = D.mul (D.mul a (D.inv a)) b :=
      (D.assoc _ _ _ (D.t_inv a).symm ((D.s_inv a).trans h)).symm
    _ = D.mul (D.unit (D.t a)) b := by rw [D.inv_right]
    _ = b := by rw [h, D.unit_left]

/-- Cancel an arrow followed by its inverse at the right of a product. -/
theorem mul_inv_cancel_right (a b : A) (h : D.s a = D.t b) :
    D.mul (D.mul a b) (D.inv b) = a := by
  rw [D.assoc a b (D.inv b) h (D.t_inv b).symm, D.inv_right, ← h]
  exact D.unit_right a

/-- A composable right inverse is the specified inverse. -/
theorem inv_unique (a b : A) (h : D.s a = D.t b)
    (hab : D.mul a b = D.unit (D.t a)) : b = D.inv a := by
  calc
    b = D.mul (D.inv a) (D.mul a b) := (inv_mul_cancel_left D a b h).symm
    _ = D.mul (D.inv a) (D.unit (D.t a)) := by rw [hab]
    _ = D.inv a := by rw [← D.s_inv a]; exact D.unit_right _

theorem inv_inv (a : A) : D.inv (D.inv a) = a := by
  symm
  apply inv_unique D (D.inv a) a (D.s_inv a)
  rw [D.inv_left, D.t_inv]

theorem inv_unit (m : M) : D.inv (D.unit m) = D.unit m := by
  symm
  apply inv_unique D (D.unit m) (D.unit m)
  · rw [D.s_unit, D.t_unit]
  · rw [D.t_unit]
    simpa only [D.t_unit] using D.unit_left (D.unit m)

theorem inv_mul (a b : A) (h : D.s a = D.t b) :
    D.inv (D.mul a b) = D.mul (D.inv b) (D.inv a) := by
  have hi : D.s (D.inv b) = D.t (D.inv a) := by
    rw [D.s_inv, D.t_inv]
    exact h.symm
  have hb : D.s b = D.t (D.mul (D.inv b) (D.inv a)) := by
    rw [D.t_mul _ _ hi, D.t_inv]
  symm
  apply inv_unique D (D.mul a b) (D.mul (D.inv b) (D.inv a))
  · rw [D.s_mul _ _ h]
    exact hb
  · rw [D.assoc a b _ h hb]
    rw [mul_inv_cancel_left D b (D.inv a) (by rw [D.t_inv]; exact h.symm)]
    rw [D.inv_right, D.t_mul _ _ h]

/-- Raw conjugation, used only at arrows with the stated endpoints. -/
def conjugate (x g : A) : A := D.mul (D.inv g) (D.mul x g)

theorem conjugate_s (x g : A) (hx : D.s x = D.t x) (hg : D.s x = D.t g) :
    D.s (conjugate D x g) = D.s g := by
  unfold conjugate
  rw [D.s_mul, D.s_mul _ _ hg]
  rw [D.s_inv, D.t_mul _ _ hg]
  exact hg.symm.trans hx

theorem conjugate_t (x g : A) (hx : D.s x = D.t x) (hg : D.s x = D.t g) :
    D.t (conjugate D x g) = D.s g := by
  unfold conjugate
  rw [D.t_mul, D.t_inv]
  rw [D.s_inv, D.t_mul _ _ hg]
  exact hg.symm.trans hx

theorem conjugate_unit_arrow (x : A) (hx : D.s x = D.t x) :
    conjugate D x (D.unit (D.s x)) = x := by
  unfold conjugate
  rw [inv_unit D, D.unit_right, hx, D.unit_left]

theorem conjugate_unit_loop (g : A) :
    conjugate D (D.unit (D.t g)) g = D.unit (D.s g) := by
  unfold conjugate
  rw [D.unit_left, D.inv_left]

theorem conjugate_comp (x g d : A) (hx : D.s x = D.t x)
    (hg : D.s x = D.t g) (hgd : D.s g = D.t d) :
    conjugate D (conjugate D x g) d = conjugate D x (D.mul g d) := by
  have hgx : D.s (D.inv g) = D.t (D.mul x g) := by
    rw [D.s_inv, D.t_mul _ _ hg]
    exact hg.symm.trans hx
  have hxd : D.s (D.mul x g) = D.t d := by
    rw [D.s_mul _ _ hg]
    exact hgd
  have hxi : D.s x = D.t (D.mul g d) := by
    rw [D.t_mul _ _ hgd]
    exact hg
  have hid : D.s (D.inv d) = D.t (D.inv g) := by
    rw [D.s_inv, D.t_inv]
    exact hgd.symm
  have hig : D.s (D.inv g) = D.t (D.mul x (D.mul g d)) := by
    rw [D.s_inv, D.t_mul _ _ hxi]
    exact hg.symm.trans hx
  unfold conjugate
  rw [D.assoc (D.inv g) (D.mul x g) d hgx hxd]
  rw [D.assoc x g d hg hgd]
  rw [← D.assoc (D.inv d) (D.inv g) (D.mul x (D.mul g d)) hid hig]
  rw [inv_mul D g d hgd]

theorem conjugate_mul (x y g : A) (hx : D.s x = D.t x)
    (hy : D.s y = D.t y) (hxy : D.s x = D.s y) (hg : D.s x = D.t g) :
    conjugate D (D.mul x y) g = D.mul (conjugate D x g) (conjugate D y g) := by
  have hgy : D.s y = D.t g := hxy.symm.trans hg
  have hcomp : D.s x = D.t y := hxy.trans hy
  have hgx : D.s (D.inv g) = D.t (D.mul x g) := by
    rw [D.s_inv, D.t_mul _ _ hg]
    exact hg.symm.trans hx
  have hxc : D.s (D.mul x g) = D.t (conjugate D y g) := by
    rw [D.s_mul _ _ hg, conjugate_t D y g hy hgy]
  have hgc : D.s g = D.t (conjugate D y g) := by
    rw [conjugate_t D y g hy hgy]
  have hty : D.t g = D.t (D.mul y g) := by
    rw [D.t_mul _ _ hgy]
    exact hgy.symm.trans hy
  symm
  calc
    D.mul (conjugate D x g) (conjugate D y g) =
        D.mul (D.inv g) (D.mul (D.mul x g) (conjugate D y g)) :=
      D.assoc _ _ _ hgx hxc
    _ = D.mul (D.inv g) (D.mul x (D.mul g (conjugate D y g))) := by
      rw [D.assoc x g _ hg hgc]
    _ = D.mul (D.inv g) (D.mul x (D.mul y g)) := by
      rw [conjugate, mul_inv_cancel_left D g (D.mul y g) hty]
    _ = conjugate D (D.mul x y) g := by
      unfold conjugate
      rw [D.assoc x y g hcomp hgy]

theorem conjugate_inv (x g : A) (hx : D.s x = D.t x)
    (hg : D.s x = D.t g) :
    conjugate D (D.inv x) g = D.inv (conjugate D x g) := by
  have hgx : D.s (D.inv g) = D.t (D.mul x g) := by
    rw [D.s_inv, D.t_mul _ _ hg]
    exact hg.symm.trans hx
  have hix : D.s (D.inv g) = D.t (D.inv x) := by
    rw [D.s_inv, D.t_inv]
    exact hg.symm
  have hxi : D.s (D.inv x) = D.t g := by
    rw [D.s_inv]
    exact hx.symm.trans hg
  unfold conjugate
  rw [inv_mul D (D.inv g) (D.mul x g) hgx, inv_mul D x g hg, inv_inv D g]
  exact (D.assoc _ _ _ hix hxi).symm

end QAlgorithms.Papers.Independent.Intakenext100.P58.S09Algebra


open QAlgorithms.Papers.Independent.Intakenext100.P58

namespace S09Loops

universe u v
variable {M : Type u} {A : Type v} (D : GroupoidData M A)

theorem base_unit (m : M) : loopBase D (loopUnit D m) = m :=
  D.s_unit m

theorem base_inverse (x : Loops D) : loopBase D (loopInverse D x) = loopBase D x := by
  exact (D.s_inv x.val).trans x.property.symm

theorem multiply_val (x y : Loops D) (h : loopBase D x = loopBase D y) :
    (loopMultiply D x y).val = D.mul x.val y.val := by
  have hc : D.s x.val = D.t y.val := h.trans y.property
  dsimp only [Loops] at x y
  simp only [loopMultiply, Loops, dif_pos hc]

theorem base_multiply (x y : Loops D) (h : loopBase D x = loopBase D y) :
    loopBase D (loopMultiply D x y) = loopBase D x := by
  change D.s (loopMultiply D x y).val = D.s x.val
  rw [multiply_val D x y h, D.s_mul _ _ (h.trans y.property)]
  exact h.symm

theorem conjugate_val (x : Loops D) (g : A) (h : loopBase D x = D.t g) :
    (loopConjugate D x g).val = D.mul (D.inv g) (D.mul x.val g) := by
  change D.s x.val = D.t g at h
  dsimp only [Loops] at x
  simp only [loopConjugate, Loops, dif_pos h]

theorem base_conjugate (x : Loops D) (g : A) (h : loopBase D x = D.t g) :
    loopBase D (loopConjugate D x g) = D.s g := by
  have hc : D.s (D.inv g) = D.t (D.mul x.val g) := by
    rw [D.s_inv, D.t_mul _ _ h]
    exact h.symm.trans x.property
  change D.s (loopConjugate D x g).val = D.s g
  rw [conjugate_val D x g h, D.s_mul _ _ hc, D.s_mul _ _ h]

theorem group_family :
    IsGroupFamily (loopBase D) (loopUnit D) (loopInverse D) (loopMultiply D) := by
  refine ⟨base_unit D, base_inverse D, base_multiply D, ?_, ?_, ?_⟩
  · intro x
    constructor
    · apply Subtype.ext
      rw [multiply_val D _ _ (base_unit D _)]
      change D.mul (D.unit (D.s x.val)) x.val = x.val
      rw [x.property, D.unit_left]
    · apply Subtype.ext
      rw [multiply_val D _ _ (base_unit D _).symm]
      exact D.unit_right x.val
  · intro x
    constructor
    · apply Subtype.ext
      rw [multiply_val D _ _ (base_inverse D x)]
      exact D.inv_left x.val
    · apply Subtype.ext
      rw [multiply_val D _ _ (base_inverse D x).symm]
      change D.mul x.val (D.inv x.val) = D.unit (D.s x.val)
      rw [D.inv_right, x.property]
  · intro x y z hxy hyz
    apply Subtype.ext
    rw [multiply_val D _ z ((base_multiply D x y hxy).trans (hxy.trans hyz)),
      multiply_val D x _ (hxy.trans (base_multiply D y z hyz).symm),
      multiply_val D x y hxy, multiply_val D y z hyz]
    exact D.assoc x.val y.val z.val (hxy.trans y.property) (hyz.trans z.property)

end S09Loops


open QAlgorithms.Papers.Independent.Intakenext100.P58
open QAlgorithms.Papers.Independent.Intakenext100.P58.S09Algebra
open S09Loops
open scoped Manifold ContDiff

universe u v

/-- The construction is algebraic and applies to every groupoid. -/
theorem loop_crossed_module {M : Type u} {A : Type v} (D : GroupoidData M A) :
    IsRightCrossedModule D (loopBase D) (loopUnit D) (loopInverse D)
      (loopMultiply D) (loopInclusion D) (loopConjugate D) := by
  refine ⟨group_family D, ?_, ?_, ?_, ?_, base_conjugate D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨rfl, x.property.symm⟩
  · intro m
    rfl
  · intro x y h
    exact multiply_val D x y h
  · intro x
    rfl
  · intro x
    apply Subtype.ext
    rw [conjugate_val D x _ (D.t_unit _).symm]
    exact conjugate_unit_arrow D x.val x.property
  · intro x g d hx hg
    apply Subtype.ext
    rw [conjugate_val D _ d ((base_conjugate D x g hx).trans hg),
      conjugate_val D x _ (hx.trans (D.t_mul g d hg).symm),
      conjugate_val D x g hx]
    exact conjugate_comp D x.val g d x.property hx hg
  · intro g
    apply Subtype.ext
    rw [conjugate_val D _ g (base_unit D _)]
    exact conjugate_unit_loop D g
  · intro x y g hxy hxg
    have hyg : loopBase D y = D.t g := hxy.symm.trans hxg
    have hc : loopBase D (loopConjugate D x g) = loopBase D (loopConjugate D y g) :=
      (base_conjugate D x g hxg).trans (base_conjugate D y g hyg).symm
    apply Subtype.ext
    rw [conjugate_val D _ g ((base_multiply D x y hxy).trans hxg),
      multiply_val D _ _ hc, multiply_val D x y hxy,
      conjugate_val D x g hxg, conjugate_val D y g hyg]
    exact conjugate_mul D x.val y.val g x.property y.property hxy hxg
  · intro x g hxg
    apply Subtype.ext
    rw [conjugate_val D _ g ((base_inverse D x).trans hxg)]
    change conjugate D (D.inv x.val) g = D.inv (loopConjugate D x g).val
    rw [conjugate_val D x g hxg]
    exact conjugate_inv D x.val g x.property hxg
  · intro x g hxg
    exact conjugate_val D x g hxg
  · intro x y hxy
    apply Subtype.ext
    change (loopConjugate D x y.val).val =
      (loopMultiply D (loopInverse D y) (loopMultiply D x y)).val
    rw [conjugate_val D x y.val (hxy.trans y.property),
      multiply_val D _ _ ((base_inverse D y).trans
        (hxy.symm.trans (base_multiply D x y hxy).symm)),
      multiply_val D x y hxy]
    rfl

theorem solution
    {n0 n1 : ℕ} {M : Type u} {A : Type v}
    [TopologicalSpace M] [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin n0)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n1)) A]
    (D : GroupoidData M A) (hLie : IsLieGroupoid (n0 := n0) (n1 := n1) D) :
    IsRightCrossedModule D (loopBase D) (loopUnit D) (loopInverse D)
      (loopMultiply D) (loopInclusion D) (loopConjugate D) :=
  loop_crossed_module D

#print axioms solution
