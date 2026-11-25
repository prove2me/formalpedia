-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.intOver_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:09.856476+00:00
-- url     : https://prove2.me/submissions/eb4a0e7d-edf6-438b-bb71-ecc378483c86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin (r + 1) → R)
    (lam : Fin r → k) (h0 : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0)) {x : R}
    (hx : IntOver k ℓ x) : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) x := by
  set ℓ' : Fin r → R := fun i => ℓ i.succ - lam i • ℓ 0 with hℓ'
  let f' : MvPolynomial (Fin r) k →+* R := (aeval ℓ' : MvPolynomial (Fin r) k →ₐ[k] R)
  letI : Algebra (MvPolynomial (Fin r) k) R := f'.toAlgebra
  let Cl := integralClosure (MvPolynomial (Fin r) k) R
  have hmem0 : ℓ 0 ∈ Cl := h0
  have hB : ∀ b, f' b ∈ Cl := fun b => Subalgebra.algebraMap_mem Cl b
  have hmem : ∀ j, ℓ j ∈ Cl := by
    intro j
    refine Fin.cases hmem0 (fun i => ?_) j
    have : ℓ i.succ = f' (X i) + f' (C (lam i)) * ℓ 0 := by
      simp [f', hℓ', Algebra.smul_def]
    rw [this]
    exact Cl.add_mem (hB _) (Cl.mul_mem (hB _) hmem0)
  have hall : ∀ p : MvPolynomial (Fin (r + 1)) k, (aeval ℓ p : R) ∈ Cl := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have := hB (C a)
      simpa [f'] using this
    | add p q hp hq => rw [map_add]; exact Cl.add_mem hp hq
    | mul_X p j hp => rw [map_mul, aeval_X]; exact Cl.mul_mem hp (hmem j)
  obtain ⟨p, hpm, hp⟩ := hx
  let g : MvPolynomial (Fin (r + 1)) k →+* Cl :=
    ((aeval ℓ : MvPolynomial (Fin (r + 1)) k →ₐ[k] R) : MvPolynomial (Fin (r + 1)) k →+* R).codRestrict
      Cl.toSubsemiring hall
  have hxC : IsIntegral Cl x := by
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  exact isIntegral_trans (R := MvPolynomial (Fin r) k) (A := Cl) x hxC
end ReciprocityTheory.ChartRestriction.G.Geo
