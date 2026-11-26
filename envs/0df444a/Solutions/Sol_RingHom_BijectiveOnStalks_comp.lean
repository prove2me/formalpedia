-- Prove2me | solution 1 for RingHom.BijectiveOnStalks.comp
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:55.521579+00:00
-- url     : https://prove2.me/submissions/8b5dddb9-435a-4e9e-b48f-e7ad83ccd725

import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Algebra_StalkIso

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Algebras and ring homomorphisms bijective on stalks

In this file we define the property of algebras and ring homomorphisms of being bijective
on stalks.

An `R`-algebra `S` is bijective on stalks if `R_q →+* S_p` is bijective for every pair of
primes `q = (algebraMap R S)⁻¹(p)`. In the literature, also the term "`R → S` identifies
local rings" is used.
-/

universe u v


variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]


namespace RingHom
namespace BijectiveOnStalks


lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.BijectiveOnStalks) (hg : g.BijectiveOnStalks) : (g.comp f).BijectiveOnStalks := by
  intro p hp
  have hq : (p.comap g).IsPrime := Ideal.IsPrime.comap g
  rw [Localization.localRingHom_comp
    (I := p.comap (g.comp f)) (p.comap g) p f (Ideal.comap_comap f g) g rfl]
  exact (hg.localRingHom p).comp (hf.localRingHom (p.comap g))


end BijectiveOnStalks
end RingHom


theorem solution.{sol_u1, sol_u2, sol_u3} : type_of% @RingHom.BijectiveOnStalks.comp.{sol_u1, sol_u2, sol_u3} := @RingHom.BijectiveOnStalks.comp.{sol_u1, sol_u2, sol_u3}
