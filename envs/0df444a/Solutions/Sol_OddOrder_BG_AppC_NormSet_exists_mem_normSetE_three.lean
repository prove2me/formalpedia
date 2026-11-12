-- Prove2me | solution 1 for OddOrder.BG.AppC.NormSet.exists_mem_normSetE_three
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:51.40449+00:00
-- url     : https://prove2.me/submissions/c498491f-3c18-40bc-b733-68233b7c909e

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSet.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod

-- ===== OddOrder/BG/AppC_NormSet.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- **BG Lemma C.2** (`q = 3`), pigeonhole step (mmd L4948): for some `c ∈ 𝔽_p` the
cubic `f_c(x) = x(x-2)(x-c) + (x-1)` has no root in `𝔽_p`.

If every `f_c` had a root `d`, then `d ∉ {0, 2}` (as `f_c(0) = -1`, `f_c(2) = 1`),
and `c` is determined by `d` (`d(d-2)(d-c) = -(d-1)` with `d(d-2) ≠ 0`), so
`c ↦ d` is injective from `𝔽_p` into `𝔽_p ∖ {0, 2}` — impossible by cardinality. -/
lemma exists_rootFree_cubic [Fact p.Prime] (hpodd : Odd p) :
    ∃ c : ZMod p, ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0 := by
  have h3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    rcases hpodd with ⟨k, hk⟩; omega
  have : NeZero p := ⟨by omega⟩
  have h02 : (0 : ZMod p) ≠ 2 := by
    intro h
    have h2cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h.symm
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h2cast
    have := Nat.le_of_dvd (by norm_num) h2cast
    omega
  by_contra hcon
  push Not at hcon
  choose g hg using hcon
  -- `g c ≠ 0` and `g c ≠ 2`, since `f_c(0) = -1`, `f_c(2) = 1`.
  have hg0 : ∀ c, g c ≠ 0 := by
    intro c h
    have hgc := hg c; rw [h] at hgc
    exact one_ne_zero (by linear_combination -hgc)
  have hg2 : ∀ c, g c ≠ 2 := by
    intro c h
    have hgc := hg c; rw [h] at hgc
    exact one_ne_zero (by linear_combination hgc)
  -- `c ↦ g c` is injective (`c` is determined by the common root `d = g c`).
  have hinj : Function.Injective g := by
    intro c1 c2 h
    have e1 := hg c1
    have e2 := hg c2
    rw [h] at e1
    have hdne : g c2 * (g c2 - 2) ≠ 0 := mul_ne_zero (hg0 c2) (sub_ne_zero.mpr (hg2 c2))
    have hfactor : g c2 * (g c2 - 2) * (g c2 - c1) = g c2 * (g c2 - 2) * (g c2 - c2) := by
      linear_combination e1 - e2
    have hsub := mul_left_cancel₀ hdne hfactor
    linear_combination -hsub
  -- Cardinality contradiction: injective map into `𝔽_p ∖ {0,2}` (size `p-2`).
  have himg : Finset.univ.image g ⊆ (Finset.univ : Finset (ZMod p)) \ {0, 2} := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨c, rfl⟩ := hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hg0 c, hg2 c⟩
  have hc1 : (Finset.univ.image g).card = p := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hcard02 : ({0, 2} : Finset (ZMod p)).card = 2 := Finset.card_pair h02
  have hdisj : Disjoint (Finset.univ.image g) ({0, 2} : Finset (ZMod p)) := by
    rw [Finset.disjoint_left]
    intro a ha ha2
    have := himg ha
    rw [Finset.mem_sdiff] at this
    exact this.2 ha2
  have key : (Finset.univ.image g).card + ({0, 2} : Finset (ZMod p)).card ≤ p :=
    calc (Finset.univ.image g).card + ({0, 2} : Finset (ZMod p)).card
        = (Finset.univ.image g ∪ {0, 2}).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = p := by rw [Finset.card_univ, ZMod.card]
  rw [hc1, hcard02] at key
  omega

lemma fCubic_eval (c x : ZMod p) :
    (fCubic p c).eval x = x * (x - 2) * (x - c) + (x - 1) := by
  simp [fCubic]

lemma fCubic_natDegree [Fact p.Prime] (c : ZMod p) : (fCubic p c).natDegree = 3 := by
  unfold fCubic
  compute_degree!

/-- A root-free `f_c` is irreducible over `𝔽_p` (a cubic with no root). -/
lemma fCubic_irreducible [Fact p.Prime] (c : ZMod p)
    (h : ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0) :
    Irreducible (fCubic p c) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, fCubic_natDegree]; omega
  · intro x hx
    rw [IsRoot, fCubic_eval] at hx
    exact h x hx

/-- An irreducible cubic over `𝔽_p` has a root in `𝔽_{p^3} = GaloisField p 3`
(its root field has cardinality `p^3`, hence is isomorphic to `GaloisField p 3`). -/
lemma exists_root_fCubic [Fact p.Prime] (c : ZMod p) (hirr : Irreducible (fCubic p c)) :
    ∃ a : GaloisField p 3, (Polynomial.aeval a) (fCubic p c) = 0 := by
  have : Fact (Irreducible (fCubic p c)) := ⟨hirr⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hne : fCubic p c ≠ 0 := hirr.ne_zero
  have : FiniteDimensional (ZMod p) (AdjoinRoot (fCubic p c)) :=
    (AdjoinRoot.powerBasis hne).basis.finiteDimensional_of_finite
  have : Finite (AdjoinRoot (fCubic p c)) := Module.finite_of_finite (ZMod p)
  have : Fintype (AdjoinRoot (fCubic p c)) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod p) (AdjoinRoot (fCubic p c)) = 3 := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, fCubic_natDegree]
  have hcard : Nat.card (AdjoinRoot (fCubic p c)) = p ^ 3 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), hfr, ZMod.card]
  let e := GaloisField.algEquivGaloisField p 3 hcard
  refine ⟨e (AdjoinRoot.root (fCubic p c)), ?_⟩
  rw [Polynomial.aeval_algHom_apply]
  have hr : (Polynomial.aeval (AdjoinRoot.root (fCubic p c))) (fCubic p c) = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root (fCubic p c)
  rw [hr, map_zero]

/-- Frobenius propagation: for `f` over `𝔽_p` and `a ∈ 𝔽_{p^q}`,
`f(a)^p = f(a^p)` (the `p`-power map fixes the `𝔽_p`-coefficients of `f`). -/
lemma aeval_pow_p [Fact p.Prime] (a : GaloisField p q) (f : (ZMod p)[X]) :
    (Polynomial.aeval a f) ^ p = Polynomial.aeval (a ^ p) f := by
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  have key : (frobenius (GaloisField p q) p).comp (Polynomial.aeval (R := ZMod p) a).toRingHom
      = (Polynomial.aeval (R := ZMod p) (a ^ p)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_C, frobenius_def]
      rw [← map_pow, ZMod.pow_card]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.aeval_X, frobenius_def]
  have h := RingHom.congr_fun key f
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobenius_def]
    using h

/-- A root `a ∈ 𝔽_{p^3}` of a root-free `f_c` does not lie in the prime field `𝔽_p`
(else `f_c` would have a root in `𝔽_p`). -/
lemma root_not_mem_range [Fact p.Prime] {c : ZMod p} {a : GaloisField p 3}
    (hroot : (Polynomial.aeval a) (fCubic p c) = 0)
    (hrf : ∀ x : ZMod p, x * (x - 2) * (x - c) + (x - 1) ≠ 0) :
    a ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  rintro ⟨b, rfl⟩
  refine hrf b ?_
  rw [← fCubic_eval, ← Polynomial.coe_aeval_eq_eval]
  exact (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
    (algebraMap (ZMod p) (GaloisField p 3)).injective).mp hroot

/-- The Frobenius-fixed elements of `𝔽_{p^q}` are exactly the prime field: if
`x^p = x` then `x ∈ 𝔽_p` (the `p` roots of `X^p - X` are the prime field). -/
lemma mem_range_of_pow_p_eq_self [Fact p.Prime] {x : GaloisField p q} (hx : x ^ p = x) :
    x ∈ Set.range (algebraMap (ZMod p) (GaloisField p q)) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set f : (GaloisField p q)[X] := X ^ p - X with hf
  have hfne : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ (Fact.out : p.Prime).one_lt
  have hfdeg : f.natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out : p.Prime).one_lt
  have hsub : (Finset.univ.image (algebraMap (ZMod p) (GaloisField p q))) ⊆ f.roots.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨b, _, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfne, Polynomial.IsRoot, hf]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← map_pow, ZMod.pow_card, sub_self]
  have hxroot : x ∈ f.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfne, Polynomial.IsRoot, hf]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
  have hcardimg : (Finset.univ.image (algebraMap (ZMod p) (GaloisField p q))).card = p := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) (GaloisField p q)).injective,
      Finset.card_univ, ZMod.card]
  have hcardroots : f.roots.toFinset.card ≤ p :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans_eq hfdeg)
  have heq : Finset.univ.image (algebraMap (ZMod p) (GaloisField p q)) = f.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardimg]; exact hcardroots)
  rw [← heq, Finset.mem_image] at hxroot
  obtain ⟨b, _, hb⟩ := hxroot
  exact ⟨b, hb⟩

/-- The cubic `f_c` is monic. -/
lemma fCubic_monic [Fact p.Prime] (c : ZMod p) : (fCubic p c).Monic := by
  unfold fCubic; monicity!

/-- `normN` over `𝔽_{p^3}` is the product of the three Frobenius conjugates. -/
lemma normN_three [Fact p.Prime] (a : GaloisField p 3) :
    normN p 3 a = a * a ^ p * a ^ (p ^ 2) := by
  rw [normN, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
  simp only [pow_zero, pow_one]

/-- **BG Lemma C.2** (`q = 3`), the lift: a root-free `f_c` yields an element of `E`
that is `≠ 1` (its Frobenius conjugates give `N(a) = N(2-a) = 1`). -/
theorem _root_.solution [Fact p.Prime] (hpodd : Odd p) :
    ∃ a : GaloisField p 3, a ∈ normSetE p 3 ∧ a ≠ 1 := by
  classical
  obtain ⟨c, hrf⟩ := exists_rootFree_cubic p hpodd
  have hirr := fCubic_irreducible p c hrf
  obtain ⟨a, hroot⟩ := exists_root_fCubic p c hirr
  have ha_notmem := root_not_mem_range p hroot hrf
  have : Fintype (GaloisField p 3) := Fintype.ofFinite _
  have : CharP (GaloisField p 3) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p 3) p]; exact ZMod.charP p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  -- `a^{p^3} = a` and the Frobenius orbit relations.
  have hpow3 : a ^ (p ^ 3) = a := by
    have hc3 : Fintype.card (GaloisField p 3) = p ^ 3 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p 3 (by norm_num)]
    rw [← hc3]; exact FiniteField.pow_card a
  have hb1 : a ^ (p ^ 2) = (a ^ p) ^ p := by rw [← pow_mul, pow_two]
  have hb2p : (a ^ (p ^ 2)) ^ p = a := by
    rw [← pow_mul, show p ^ 2 * p = p ^ 3 from by ring, hpow3]
  -- `a, a^p, a^{p²}` are distinct.
  have hd01 : a ^ p ≠ a := fun h => ha_notmem (mem_range_of_pow_p_eq_self p 3 h)
  have hd02 : a ^ (p ^ 2) ≠ a := fun h => hd01 (by have := hb2p; rwa [h] at this)
  have hd12 : a ^ p ≠ a ^ (p ^ 2) := fun h => hd02 (by
    calc a ^ (p ^ 2) = (a ^ p) ^ p := hb1
      _ = (a ^ (p ^ 2)) ^ p := by rw [h]
      _ = a := hb2p)
  -- The mapped cubic `g` is monic of degree 3 with roots `a, a^p, a^{p²}`.
  set g : (GaloisField p 3)[X] := (fCubic p c).map (algebraMap (ZMod p) (GaloisField p 3)) with hg
  have hgeval : ∀ x : GaloisField p 3, g.eval x = (Polynomial.aeval x) (fCubic p c) := by
    intro x; rw [hg, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hgmonic : g.Monic := (fCubic_monic p c).map _
  have hgne : g ≠ 0 := hgmonic.ne_zero
  have hgdeg : g.natDegree = 3 := by rw [hg, (fCubic_monic p c).natDegree_map, fCubic_natDegree]
  have haevalp : (Polynomial.aeval (a ^ p)) (fCubic p c) = 0 := by
    rw [← aeval_pow_p, hroot, zero_pow hp0]
  have haevalp2 : (Polynomial.aeval (a ^ (p ^ 2))) (fCubic p c) = 0 := by
    rw [hb1, ← aeval_pow_p, haevalp, zero_pow hp0]
  have hra : g.eval a = 0 := by rw [hgeval]; exact hroot
  have hrap : g.eval (a ^ p) = 0 := by rw [hgeval]; exact haevalp
  have hrap2 : g.eval (a ^ (p ^ 2)) = 0 := by rw [hgeval]; exact haevalp2
  -- The roots multiset of `g` is exactly `{a, a^p, a^{p²}}`.
  set s : Multiset (GaloisField p 3) := {a, a ^ p, a ^ (p ^ 2)} with hs
  have hs_card : s.card = 3 := rfl
  have hs_nodup : s.Nodup := by
    simp only [hs, Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, not_or, and_true]
    exact ⟨⟨fun h => hd01 h.symm, fun h => hd02 h.symm⟩, fun h => hd12 h⟩
  have hs_le : s ≤ g.roots := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ s
    · rw [Multiset.count_eq_one_of_mem hs_nodup hx]
      refine Multiset.one_le_count_iff_mem.mpr ?_
      rw [Polynomial.mem_roots hgne]
      simp only [hs, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hra
      · exact hrap
      · exact hrap2
    · rw [Multiset.count_eq_zero.mpr hx]; exact Nat.zero_le _
  have hcard_le : g.roots.card ≤ s.card := by
    rw [hs_card]; exact (Polynomial.card_roots' g).trans_eq hgdeg
  have hgroots : g.roots = s := (Multiset.eq_of_le_of_card_le hs_le hcard_le).symm
  have hgprod : g = (s.map (fun r => X - C r)).prod := by
    rw [← hgroots]
    exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hgmonic
      (by rw [hgroots, hs_card]; exact hgdeg.symm)).symm
  -- Evaluate at 0 and 2: `g(0) = -(a a^p a^{p²}) = -N(a)`, `g(2) = N(2-a)`.
  have hprodeval : ∀ x : GaloisField p 3,
      g.eval x = (x - a) * (x - a ^ p) * (x - a ^ (p ^ 2)) := by
    intro x
    rw [hgprod, hs]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have h2pow : (2 : GaloisField p 3) ^ p = 2 := by
    rw [show (2 : GaloisField p 3) = algebraMap (ZMod p) (GaloisField p 3) 2 from
      (map_ofNat _ 2).symm, ← map_pow, ZMod.pow_card]
  have hfc0 : (fCubic p c).eval 0 = -1 := by rw [fCubic_eval]; ring
  have hfc2 : (fCubic p c).eval 2 = 1 := by rw [fCubic_eval]; ring
  have hN_a : normN p 3 a = 1 := by
    have h0 : g.eval 0 = -1 := by
      rw [hgeval,
        show (0 : GaloisField p 3) = algebraMap (ZMod p) (GaloisField p 3) 0 from
          (map_zero _).symm,
        Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval, hfc0, map_neg, map_one]
    rw [hprodeval] at h0
    rw [normN_three]
    linear_combination -h0
  have hN_2a : normN p 3 (2 - a) = 1 := by
    have h2 : g.eval 2 = 1 := by
      rw [hgeval,
        show (2 : GaloisField p 3) = algebraMap (ZMod p) (GaloisField p 3) 2 from
          (map_ofNat _ 2).symm,
        Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval, hfc2, map_one]
    rw [hprodeval] at h2
    rw [normN_three]
    have e1 : (2 - a) ^ p = 2 - a ^ p := by rw [sub_pow_char, h2pow]
    have e2 : (2 - a) ^ (p ^ 2) = 2 - a ^ (p ^ 2) := by
      have hpp : (2 - a) ^ (p ^ 2) = ((2 - a) ^ p) ^ p := by rw [← pow_mul, pow_two]
      rw [hpp, e1, sub_pow_char, h2pow, ← hb1]
    rw [e1, e2]
    linear_combination h2
  exact ⟨a, ⟨hN_a, hN_2a⟩, fun h => ha_notmem ⟨1, by rw [h]; simp⟩⟩

end OddOrder.BG.AppC.NormSet
