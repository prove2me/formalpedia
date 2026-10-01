-- Prove2me | solution 1 for ShorAlgorithms.Reduction.orderOf_eq_lcm
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:21:43.537138+00:00
-- url     : https://prove2.me/submissions/41fe1df6-e099-4e7d-8f59-50b1bcf4a207

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_localOrder
open ShorAlgorithms.Reduction
namespace AShor
noncomputable section

def localMap (n : ℕ) : (ZMod n)ˣ →* ∀ p : n.primeFactors, (ZMod (p.1 ^ n.factorization p.1))ˣ :=
  MonoidHom.pi fun p => Units.map
    (ZMod.castHom (Nat.ordProj_dvd n p.1) (ZMod (p.1 ^ n.factorization p.1))).toMonoidHom

theorem localMap_injective (n : ℕ) (hn : 0 < n) : Function.Injective (localMap n) := by
  intro u v huv
  apply Units.ext
  apply (ZMod.equivPi n hn.ne').injective
  funext p
  have hE (a : ZMod n) : ZMod.equivPi n hn.ne' a p =
      ZMod.castHom (Nat.ordProj_dvd n p.1) (ZMod (p.1 ^ n.factorization p.1)) a := by
    exact RingHom.congr_fun (Subsingleton.elim
      ((Pi.evalRingHom (fun p : n.primeFactors => ZMod (p.1 ^ n.factorization p.1)) p).comp
        (ZMod.equivPi n hn.ne').toRingHom)
      (ZMod.castHom (Nat.ordProj_dvd n p.1) (ZMod (p.1 ^ n.factorization p.1)))) a
  rw [hE,hE]
  exact congrArg (fun w : (ZMod (p.1 ^ n.factorization p.1))ˣ => (w : ZMod (p.1 ^ n.factorization p.1))) (congrFun huv p)

theorem order_local (n : ℕ) (hn : 0 < n) (u : (ZMod n)ˣ) :
    orderOf u = n.primeFactors.lcm (localOrder n u) := by
  rw [←orderOf_injective (localMap n) (localMap_injective n hn) u,Pi.orderOf]
  change Finset.univ.lcm (fun p : n.primeFactors => localOrder n u p.1) = n.primeFactors.lcm (localOrder n u)
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro p hp
    exact Finset.dvd_lcm p.2
  · apply Finset.lcm_dvd
    intro p hp
    exact Finset.dvd_lcm (Finset.mem_univ (⟨p,hp⟩ : n.primeFactors))
end
end AShor

theorem solution (n : ℕ) (hn : 0 < n) (u : (ZMod n)ˣ) :
    orderOf u = n.primeFactors.lcm (localOrder n u) := AShor.order_local n hn u
