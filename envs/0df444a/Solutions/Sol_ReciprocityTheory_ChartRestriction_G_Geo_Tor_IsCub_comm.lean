-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:28.627497+00:00
-- url     : https://prove2.me/submissions/e8b1dfbf-689a-4daf-b2e1-d61640b4e30f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add

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
variable {A U : Type} [CommGroup A] [CommGroup U]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
theorem _root_.solution (k : ℕ) (a m b x : A) (Sa Sm Sam τa τy τay : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : τay * θ a (b ^ k) m = τa * τy) (h₃ : τy * cubN θ k 1 b m = Sm ^ k) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * τa * (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * Sam) =
      cubN θ k a b (x * m) * (θ a (x * m) b)⁻¹ * Sa * (cubN θ k (a * b ^ k) m x * (θ (a * b ^ k) x m)⁻¹ * τay) := by
  have rot : ∀ p q r, θ p q r = θ q r p := fun p q r => by rw [h.s01 p q r, h.s12 q p r]
  have hmx : θ m x b = θ b x m := by rw [h.s01 m x b, h.s12 x m b, h.s01 x b m]
  have eSam : Sam = Sa * Sm ^ k * (cubN θ k a m b)⁻¹ := eq_mul_inv_of_mul_eq h₁
  have eτay : τay = τa * τy * (θ a (b ^ k) m)⁻¹ := eq_mul_inv_of_mul_eq h₂
  have eSm : Sm ^ k = τy * cubN θ k 1 b m := h₃.symm
  have e1 : cubN θ k a m (x * b) =
      θ (a * m ^ k) x b * cubN θ k a m x * cubN θ k a m b * (θ a x b * θ m x b ^ k)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← _root_.mul_assoc]; exact h.N_add k a m x b
  have e2 : cubN θ k a b (x * m) =
      θ (a * b ^ k) x m * cubN θ k a b x * cubN θ k a b m * (θ a x m * θ b x m ^ k)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← _root_.mul_assoc]; exact h.N_add k a b x m
  have c1 := h.coc a (m ^ k) (b ^ k) x
  have c2 := h.coc a (b ^ k) (m ^ k) x
  rw [_root_.mul_comm (b ^ k) (m ^ k), ← h.s01 (m ^ k) (b ^ k) x] at c2
  have c3 := h.coc x b m a
  have c4 := h.coc x m b a
  rw [_root_.mul_comm m b, h.s01 m b a] at c4
  have c1' := eq_mul_inv_of_mul_eq c1
  have c2' := eq_mul_inv_of_mul_eq c2
  have c3' := eq_mul_inv_of_mul_eq c3
  have c4' := eq_mul_inv_of_mul_eq c4
  rw [eSam, eτay, eSm, e1, e2, h.N_split k (a * m ^ k) b x, h.N_split k (a * b ^ k) m x, h.N_split k a m x,
    h.N_split k a b x, h.N_split k a b m, c1', c2', rot a (x * b) m, rot a (x * m) b, c3', c4', rot a x b,
    rot a x m, hmx]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
