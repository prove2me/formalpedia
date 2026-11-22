-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_cub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:02.861613+00:00
-- url     : https://prove2.me/submissions/3067a5c5-d8b8-45ed-be8f-72ab60da67e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : thK, h ((lift x (lift x' y)).left ≫ thφ G (x3 G) I) ^ thε I =
      h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G).left)⁻¹ := by
  have e : ∀ I : thK, (lift x (lift x' y)).left ≫ thφ G (x3 G) I = (psum G ![x, x', y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x (lift x' y))) (x3 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])))
  refine (Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _
    (fun I => h (psum G ![x, x', y] I).left ^ ((-1 : ℤ) ^ (3 - I.card)))
    (fun I => congrArg (fun q => h q ^ thε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [zpow_neg, zpow_one]
  ac_rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
