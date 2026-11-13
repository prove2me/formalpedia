-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.thompson_normal_p_complement_of_local_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:34.672126+00:00
-- url     : https://prove2.me/submissions/33fffa41-22fc-4199-ad3e-a7a03f10ac73

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_CentralizerCenter.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplementFinal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch07_normal_thompsonJ_of_le_opCore
import Theorems.Thm_OddOrder_Isaacs_Ch07_thompsonJ_le_opCore_of_normal_J_hypotheses
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv
import Theorems.Thm_OddOrder_Isaacs_Ch07_twoSubgroups_commutative_of_minimal_counterexample
import Theorems.Thm_OddOrder_Isaacs_Ch07_sylow_isCoatom_of_minimal_counterexample
import Theorems.Thm_OddOrder_Isaacs_Ch07_exists_lexicographically_maximal_badNormalizerPSubgroup
import Theorems.Thm_OddOrder_Isaacs_Ch07_maximal_badNormalizer_eq_opCore
import Theorems.Thm_OddOrder_Isaacs_Ch07_maximal_badNormalizer_quotient_hasNormalPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch07_isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch07_oPiPrimeCore_eq_bot_of_minimal_counterexample

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6** (normal-J theorem, unconditional).

The full theorem (Isaacs L3832) states:

> Suppose `G` is `p`-solvable with `p ≠ 2`, Sylow `2`-subgroups of `G` are abelian,
> `O_{p'}(G) = 1`, and `P = C_G(Z(P))` for some `P ∈ Syl_p(G)`.  Then `J(P) ⊴ G`.

The textbook proof (Isaacs p.209-214) is an **8-step Goldschmidt-style argument**:
Steps 1-7 establish `J(P) ≤ O_p(G)` using Thm 7.5 (normal-P), Ch.4 Cor 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`), Ch.6 Thm 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`), and Hall-Higman 3.21.
Step 8 propagates normality from `O_p(G)` to `G` via Thm 7.2
(`thompsonJ_eq_of_le_of_le`) + characteristic-of-characteristic transport.

All eight steps are landed as proved theorems: Steps 4+5 =
`step4_5_normal_J_hypotheses` (`P = UA` and `|Ā| = p`, both using Step 3's IH
internally), Step 8 = `step8a_PBar_normal_GBar` + `step8b_pullback_normal_P`
(Thm 7.5 application + pullback).  Nothing is axiomatized: `normal_J` is
sorry-free and axiom-clean (asserted in `AxiomsCheck`). -/
theorem normal_J
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  have h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    thompsonJ_le_opCore_of_normal_J_hypotheses P hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center
  exact normal_thompsonJ_of_le_opCore P h_le

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement

/-- Normal `p`-complements pass to quotient groups.

This is the "homomorphic images" inheritance used at the start of Isaacs §7C, before
the seven-step minimum-counterexample argument.  The complement is the quotient image
of the upstairs normal complement, and `Sylow.mapSurjective` matches each Sylow
subgroup of the quotient with the image of a Sylow subgroup upstairs. -/
theorem hasNormalPComplement_quotient
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (L : Subgroup G) [L.Normal] :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ L) := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  let f : G →* G ⧸ L := QuotientGroup.mk' L
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective L
  refine ⟨N.map f, Subgroup.Normal.map hN_normal f hf_surj, fun Qbar => ?_⟩
  obtain ⟨Q, hQ_mapSurj⟩ := Sylow.mapSurjective_surjective (p := p) hf_surj Qbar
  have hQ_map : (Q : Subgroup G).map f = (Qbar : Subgroup (G ⧸ L)) := by
    have h := congrArg (fun R : Sylow p (G ⧸ L) => (R : Subgroup (G ⧸ L))) hQ_mapSurj
    simpa [f, Sylow.coe_mapSurjective] using h
  have hQ_compl : Subgroup.IsComplement' N (Q : Subgroup G) := hN_compl Q
  have hp_ndvd_N : ¬ p ∣ Nat.card N := by
    rw [← hQ_compl.index_eq_card]
    exact Q.not_dvd_index
  obtain ⟨k, hQ_card⟩ : ∃ k, Nat.card (Q : Subgroup G) = p ^ k :=
    IsPGroup.iff_card.mp Q.isPGroup'
  have h_coprime : Nat.Coprime (Nat.card N) (Nat.card (Q : Subgroup G)) := by
    rw [hQ_card]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
  have h_image_compl :
      Subgroup.IsComplement' (N.map f) ((Q : Subgroup G).map f) :=
    hQ_compl.map_mk' h_coprime L
  rwa [hQ_map] at h_image_compl

/-- Normal `p`-complements pass to homomorphic images of subgroups.

This is the subgroup-image form of the inheritance principle quoted in Isaacs §7C.
It will be used for quotient images of `N_G(X)` and `C_G(X)` in Steps 2 and 3. -/
theorem hasNormalPComplement_subgroup_map
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (φ : G →* K) (H : Subgroup G)
    (hH : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥H) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥(H.map φ) := by
  classical
  let φH : ↥H →* K := φ.comp H.subtype
  have hQuot : OddOrder.Isaacs.Ch05.HasNormalPComplement p (↥H ⧸ φH.ker) :=
    hasNormalPComplement_quotient (G := ↥H) hH φH.ker
  have hRange : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥φH.range :=
    hasNormalPComplement_of_mulEquiv (QuotientGroup.quotientKerEquivRange φH) hQuot
  have hRange_eq : φH.range = H.map φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.property, rfl⟩
    · rintro ⟨x, hxH, rfl⟩
      exact ⟨⟨x, hxH⟩, rfl⟩
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hRange_eq) hRange

/-- **Isaacs Thm 7.1, Step 7 reduction** (normal `J(P)` case).

This helper packages the last observation in Isaacs Step 7: once `J(P) ⊴ G`, the
normalizer `N_G(J(P))` is all of `G`, so a normal `p`-complement in that normalizer
transports across `N_G(J(P)) ≃* G`.  The public theorem below now obtains
`J(P) ⊴ G` from the real `normal_J` hypotheses instead of exposing it as the
main theorem's raw forward assumption. -/
private theorem thompson_normal_p_complement_of_thompsonJ_normal
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hNJP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
          ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G)))
    (hJ_normal : (Subgroup.thompsonJ (P : Subgroup G) p).Normal) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  -- J(P) ⊴ G implies N_G(J(P)) = ⊤.
  have h_norm_top :
      Subgroup.normalizer
        ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hJ_normal
  set NG : Subgroup G :=
    Subgroup.normalizer
      ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G) with hNG_def
  -- Compose ↥NG ≃* ↥⊤ ≃* G.
  let eqEquiv : NG ≃* (⊤ : Subgroup G) := MulEquiv.subgroupCongr h_norm_top
  let topToG : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let e : ↥NG ≃* G := eqEquiv.trans topToG
  exact hasNormalPComplement_of_mulEquiv e hNJP

/-- **Isaacs Thm 7.1, Step 7** (Thompson normal `p`-complement theorem,
conditional on Steps 2-6 of the minimum-counterexample proof).

The old scaffold for this theorem assumed `J(P) ⊴ G` directly.  This version
replaces that raw forward normality hypothesis by the actual five hypotheses of
Isaacs Thm 7.6 (`normal_J`): `p ≠ 2`, `p`-separability, abelian Sylow `2`-subgroups,
`O_{p'}(G)=1`, and `C_G(Z(P)) = P`.

Thus the remaining §7C work is exactly Steps 1-6: starting from the textbook
hypotheses that `C_G(Z(P))` and `N_G(J(P))` have normal `p`-complements, the
minimum-counterexample argument must derive these normal-J hypotheses.  Once they
are available, Step 7 is now sorry-free: apply `normal_J`, so `N_G(J(P)) = G`, and
transport the normal `p`-complement from the normalizer to `G`. -/
theorem thompson_normal_p_complement
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (hNJP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
          ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  exact
    thompson_normal_p_complement_of_thompsonJ_normal P hNJP
      (normal_J P hp2 h_pSolvable h2abelian h_oPiPrime_trivial h_centralizer_center)

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section QuotientCenter

/-- Centers commute with a homomorphism that is injective on the subgroup in question.

This restricted-injectivity form applies both to embeddings into an ambient group and
to quotient maps whose kernel is disjoint from a `p`-subgroup. -/
theorem center_map_subtype_map_of_restrict_injective
    {H : Type*} [Group H] (f : G →* H) {P : Subgroup G}
    (hf : Function.Injective (f.comp P.subtype)) :
    (Subgroup.center ↥(P.map f)).map (P.map f).subtype =
      ((Subgroup.center ↥P).map P.subtype).map f := by
  ext x
  constructor
  · intro hx
    have hx_center := Subgroup.mem_center_map_subtype_iff.mp hx
    obtain ⟨z, hzP, hzx⟩ := hx_center.1
    refine ⟨z, Subgroup.mem_center_map_subtype_iff.mpr ⟨hzP, ?_⟩, hzx⟩
    intro w hw
    have hcomm_f := hx_center.2 (f w) ⟨w, hw, rfl⟩
    rw [← hzx] at hcomm_f
    have hsub :
        (f.comp P.subtype) (⟨w, hw⟩ * ⟨z, hzP⟩) =
          (f.comp P.subtype) (⟨z, hzP⟩ * ⟨w, hw⟩) := by
      change f (w * z) = f (z * w)
      simpa only [map_mul] using hcomm_f
    exact congrArg Subtype.val (hf hsub)
  · rintro ⟨z, hz, rfl⟩
    have hz_center := Subgroup.mem_center_map_subtype_iff.mp hz
    apply Subgroup.mem_center_map_subtype_iff.mpr
    refine ⟨⟨z, hz_center.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg f (hz_center.2 w hw)

end QuotientCenter

section LocalHypothesisTransport

/-- The two local normal-complement hypotheses are invariant under a group
isomorphism. -/
theorem HasThompsonLocalPComplements.map_mulEquiv
    {H : Type*} [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : HasThompsonLocalPComplements p P) (e : G ≃* H) :
    HasThompsonLocalPComplements p (P.map e.toMonoidHom) := by
  have heP : Function.Injective (e.toMonoidHom.comp P.subtype) :=
    e.injective.comp P.subtype_injective
  have hCenter :
      (Subgroup.center ↥(P.map e.toMonoidHom)).map
          (P.map e.toMonoidHom).subtype =
        ((Subgroup.center ↥P).map P.subtype).map e.toMonoidHom :=
    center_map_subtype_map_of_restrict_injective e.toMonoidHom heP
  constructor
  · have hImage :=
      hasNormalPComplement_subgroup_map e.toMonoidHom
        (Subgroup.centralizer
          (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)) hP.1
    have hLocalizer :
        (Subgroup.centralizer
            (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)).map
              e.toMonoidHom =
          Subgroup.centralizer
            (((Subgroup.center ↥(P.map e.toMonoidHom)).map
              (P.map e.toMonoidHom).subtype : Subgroup H) : Set H) := by
      rw [hCenter]
      simpa only [Subgroup.coe_map] using
        (Subgroup.map_centralizer_eq_of_bijective
          (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)
          e.toMonoidHom e.bijective)
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hLocalizer) hImage
  · have hImage :=
      hasNormalPComplement_subgroup_map e.toMonoidHom
        (Subgroup.normalizer ((Subgroup.thompsonJ P p : Subgroup G) : Set G)) hP.2
    have hJ :
        Subgroup.thompsonJ (P.map e.toMonoidHom) p =
          (Subgroup.thompsonJ P p).map e.toMonoidHom :=
      Subgroup.thompsonJ_map_of_injective e.injective P p
    have hLocalizer :
        (Subgroup.normalizer
            ((Subgroup.thompsonJ P p : Subgroup G) : Set G)).map e.toMonoidHom =
          Subgroup.normalizer
            ((Subgroup.thompsonJ (P.map e.toMonoidHom) p : Subgroup H) : Set H) := by
      rw [hJ]
      exact Subgroup.map_normalizer_eq_of_bijective _ e.bijective
    exact hasNormalPComplement_of_mulEquiv
      (MulEquiv.subgroupCongr hLocalizer) hImage

/-- Local normal-complement hypotheses at one Sylow subgroup propagate to all
Sylow subgroups by conjugacy. -/
theorem HasThompsonLocalPComplements.of_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (P Q : Sylow p G)
    (hP : HasThompsonLocalPComplements p (P : Subgroup G)) :
    HasThompsonLocalPComplements p (Q : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmap :
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
    change (MulAut.conj g • (P : Subgroup G)) = (Q : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have h := hP.map_mulEquiv (MulAut.conj g)
  rw [hmap] at h
  exact h

/-- The textbook hypotheses at a chosen Sylow subgroup are equivalent to their
intrinsic all-Sylow form. -/
theorem hasThompsonPComplementHypothesis_iff
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    HasThompsonPComplementHypothesis p G ↔
      HasThompsonLocalPComplements p (P : Subgroup G) := by
  constructor
  · exact fun h => h P
  · intro h Q
    exact h.of_sylow P Q

end LocalHypothesisTransport

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_CentralizerCenter.lean =====
namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section MinimalCounterexampleStepFive

/-- **Isaacs Theorem 7.1, Step 5.**

In a minimal counterexample, `C_G(Z(P)) = P`.  The inclusion `P ≤ C_G(Z(P))`
is immediate from centrality.  Step 4 makes `P` maximal.  The centralizer cannot
be all of `G`, since its assumed normal `p`-complement would then transport to
one in `G`; maximality therefore forces equality. -/
theorem centralizer_center_eq_sylow_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map
          (P : Subgroup G).subtype : Subgroup G) : Set G) =
      (P : Subgroup G) := by
  classical
  have hP_max : IsCoatom (P : Subgroup G) :=
    sylow_isCoatom_of_minimal_counterexample P hHyp ih hG hQuotient
  set Z : Subgroup G :=
    (Subgroup.center (P : Subgroup G)).map
      (P : Subgroup G).subtype with hZ_def
  set C : Subgroup G := Subgroup.centralizer (Z : Set G) with hC_def
  have hP_le_C : (P : Subgroup G) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZ_def] at hz
    obtain ⟨z₀, hz₀_center, rfl⟩ := hz
    have hcomm :=
      (Subgroup.mem_center_iff.mp hz₀_center) ⟨s, hs⟩
    have hcomm_ambient :=
      congrArg (Subgroup.subtype (P : Subgroup G)) hcomm
    simpa [mul_comm] using hcomm_ambient.symm
  have hC_complement :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥C := by
    simpa only [hC_def, hZ_def] using (hHyp P).1
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    let e : ↥C ≃* G :=
      (MulEquiv.subgroupCongr hC_top).trans Subgroup.topEquiv
    exact hG (hasNormalPComplement_of_mulEquiv e hC_complement)
  have hC_eq_P : C = (P : Subgroup G) :=
    (hP_max.le_iff_eq hC_ne_top).mp hP_le_C
  simpa only [hC_def, hZ_def] using hC_eq_P

end MinimalCounterexampleStepFive

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplementFinal.lean =====
namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section ThompsonNormalPComplement

/-- **Isaacs Theorem 7.1** (Thompson normal `p`-complement theorem).

Let `p ≠ 2` and let `P` be a Sylow `p`-subgroup of a finite group `G`.  If
`C_G(Z(P))` and `N_G(J(P))` both have normal `p`-complements, then so does `G`.

The proof converts the hypotheses at `P` to the conjugacy-invariant all-Sylow
form and argues by strong induction on `|G|`.  In a counterexample, Steps 1–2
identify the maximal bad subgroup with `O_p(G)` and construct a normal
`p`-complement in the quotient.  Steps 3, 5, and 6 give `O_{p'}(G) = 1`,
`C_G(Z(P)) = P`, and abelian `2`-subgroups.  Theorem 7.6 then makes `J(P)`
normal, so the assumed complement in its normalizer is a complement in `G`. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (hCZ : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map
          (P : Subgroup G).subtype : Subgroup G) : Set G)))
    (hNJ : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
        ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  have hHyp : HasThompsonPComplementHypothesis p G := by
    rw [hasThompsonPComplementHypothesis_iff P]
    exact ⟨hCZ, hNJ⟩
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H = n →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H
  suffices hmain : motive (Nat.card G) by
    exact hmain G rfl hHyp
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ hH_card hH_hyp
  by_contra hH
  have ih' :
      ∀ (K : Type u) [Group K] [Finite K],
        Nat.card K < Nat.card H →
        HasThompsonPComplementHypothesis p K →
        OddOrder.Isaacs.Ch05.HasNormalPComplement p K := by
    intro K _ _ hK_card hK_hyp
    exact ih (Nat.card K) (by simpa only [hH_card] using hK_card)
      K rfl hK_hyp
  obtain ⟨U, hU_bad, hU_weight_max, hU_card_max⟩ :=
    exists_lexicographically_maximal_badNormalizerPSubgroup hH
  have hU_eq : U = OddOrder.Isaacs.Ch01.opCore p H :=
    maximal_badNormalizer_eq_opCore hH_hyp ih' hU_bad
      hU_weight_max hU_card_max
  subst U
  have hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (H ⧸ OddOrder.Isaacs.Ch01.opCore p H) :=
    maximal_badNormalizer_quotient_hasNormalPComplement ih' hU_bad
      hU_weight_max hU_card_max
  let Q : Sylow p H := default
  have h_pSolvable :
      OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
    isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
      (OddOrder.Isaacs.Ch01.opCore_isPGroup p H) hQuotient
  have h_oPiPrime_trivial :
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ :=
    oPiPrimeCore_eq_bot_of_minimal_counterexample Q hH_hyp ih' hH
  have h_centralizer_center :
      Subgroup.centralizer
          (((Subgroup.center (Q : Subgroup H)).map
            (Q : Subgroup H).subtype : Subgroup H) : Set H) =
        (Q : Subgroup H) :=
    centralizer_center_eq_sylow_of_minimal_counterexample
      Q hH_hyp ih' hH hQuotient
  have h2abelian :
      ∀ S : Subgroup H, IsPGroup 2 S →
        ∀ x y : ↥S, x * y = y * x :=
    twoSubgroups_commutative_of_minimal_counterexample
      Q hp2 hH_hyp ih' hH hQuotient
  exact hH
    (thompson_normal_p_complement Q hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center (hH_hyp Q).2)

end ThompsonNormalPComplement

end OddOrder.Isaacs.Ch07
