-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.oPiPrimeCore_eq_bot_of_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:56:49.039965+00:00
-- url     : https://prove2.me/submissions/cb8c23d9-4024-45ca-a157-1e1fe988c595

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_Subgroup_thompsonJ_ne_bot
import Theorems.Thm_OddOrder_Isaacs_Ch02_normalizer_map_of_coprime_kernel
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv
import Theorems.Thm_OddOrder_Isaacs_Ch07_thompsonJ_map_of_coprime_kernel
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_quotient_of_isPiGroup_compl

-- ===== OddOrder/GroupTheory/ThompsonSubgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

/-- `J(P) ≤ P`: Thompson subgroup は `P` の部分群. -/
theorem thompsonJ_le (P : Subgroup G) (p : ℕ) : thompsonJ P p ≤ P := by
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact hE.1

end Subgroup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement

/-- **Isaacs Lem 7.7 (b)** (image of centralizer under p'-quotient).

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`C_Ḡ(P̄) = (C_G(P)).map f`.

書籍 p.215-216 の証明 (Lem 2.17 の "short extension"):
1. ⊇ は明らか (image of centralizer ⊆ centralizer of image).
2. ⊆: Lem 2.17 (a) で `N̄(P̄) = (N_G(P)).map f`. `Cbar ≤ Nbar` (centralizer ≤ normalizer).
   correspondence: `X := N_G(P) ⊓ Cbar.comap f` とおく ⇒ `X.map f = Cbar`.
   `⁅P, X⁆.map f = ⁅Pbar, Cbar⁆ = ⊥` ⇒ `⁅P, X⁆ ≤ ker f = N`. かつ `⁅P, X⁆ ≤ P`
   (X ≤ N_G(P) なので). 従って `⁅P, X⁆ ≤ P ⊓ N = ⊥` (coprime), 即ち `X ≤ C_G(P)`. -/
theorem centralizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N) := by
  classical
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  set Pbar : Subgroup (G ⧸ N) := P.map f with hPbar_def
  set Cbar : Subgroup (G ⧸ N) := Subgroup.centralizer (Pbar : Set (G ⧸ N)) with hCbar_def
  -- Coprime: P ⊓ N = ⊥
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  -- ker f = N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  refine le_antisymm ?_ ?_
  · -- ⊆ direction (hard)
    -- Cbar ≤ Nbar
    have hCbar_le_Nbar : Cbar ≤ Subgroup.normalizer Pbar := centralizer_le_normalizer Pbar
    -- Nbar = (N_G(P)).map f by Lem 2.17 (a)
    have hN_eq : Subgroup.normalizer Pbar = (Subgroup.normalizer P).map f := by
      rw [hPbar_def, hf_def]
      exact OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel hp_coprime hP_pgroup
    -- X := N_G(P) ⊓ (Cbar.comap f).  X.map f = Cbar (correspondence).
    set X : Subgroup G := Subgroup.normalizer P ⊓ Cbar.comap f with hX_def
    have hX_map_eq : X.map f = Cbar := by
      apply le_antisymm
      · rintro _ ⟨y, ⟨_hy_N, hy_C⟩, rfl⟩
        exact (Subgroup.mem_comap.mp hy_C : f y ∈ Cbar)
      · intro c hc
        have hc_Nbar : c ∈ Subgroup.normalizer Pbar := hCbar_le_Nbar hc
        rw [hN_eq] at hc_Nbar
        obtain ⟨n, hn_NgP, hn_eq⟩ := hc_Nbar
        refine ⟨n, ⟨hn_NgP, ?_⟩, hn_eq⟩
        change f n ∈ Cbar
        rw [hn_eq]
        exact hc
    -- Claim: X ≤ centralizer P
    have hX_le_C : X ≤ Subgroup.centralizer (P : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      -- ⁅X, P⁆ = ⊥: ⊆ N (commutator maps to ⊥) and ⊆ P (X ≤ N_G(P)), so ⊆ P ⊓ N = ⊥.
      have h_map_bot : (⁅X, P⁆ : Subgroup G).map f = ⊥ := by
        rw [Subgroup.map_commutator, hX_map_eq]
        -- goal: ⁅Cbar, Pbar⁆ = ⊥
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
      have h_comm_le_N : (⁅X, P⁆ : Subgroup G) ≤ N := by
        rw [← hf_ker]
        exact (Subgroup.map_eq_bot_iff _).mp h_map_bot
      have h_comm_le_P : (⁅X, P⁆ : Subgroup G) ≤ P := by
        rw [Subgroup.commutator_le]
        intro x hx_X p hp_P
        -- x ∈ X ≤ N_G(P), so x p x⁻¹ ∈ P. Then ⁅x, p⁆ = x p x⁻¹ p⁻¹ ∈ P.
        have hx_N : x ∈ Subgroup.normalizer P := hx_X.1
        have hxpx : x * p * x⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp hx_N p).mp hp_P
        change x * p * x⁻¹ * p⁻¹ ∈ P
        exact P.mul_mem hxpx (P.inv_mem hp_P)
      -- ⁅X, P⁆ ≤ P ⊓ N = ⊥
      have h_comm_le_bot : (⁅X, P⁆ : Subgroup G) ≤ ⊥ := by
        have h_inf : (⁅X, P⁆ : Subgroup G) ≤ P ⊓ N := le_inf h_comm_le_P h_comm_le_N
        rw [hP_inf_N] at h_inf
        exact h_inf
      exact le_bot_iff.mp h_comm_le_bot
    -- Cbar = X.map f ⊆ (centralizer P).map f
    rw [← hX_map_eq]
    exact Subgroup.map_mono hX_le_C
  · -- ⊇ direction (easy): (C_G(P)).map f ≤ Cbar
    rintro - ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro - ⟨p, hp, rfl⟩
    -- c centralizes p in G ⇒ f(c) centralizes f(p)
    have hcp : c * p = p * c := (Subgroup.mem_centralizer_iff.mp hc p hp).symm
    rw [← map_mul, ← map_mul]
    exact congrArg f hcp.symm

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

/-- If `N ⊴ G` is a normal `p'`-subgroup, then a normal `p`-complement in
`N_G(P)` pushes to a normal `p`-complement in `N_{G/N}(Pbar)`.

This combines subgroup-image inheritance with Isaacs Lemma 7.7(a). -/
theorem hasNormalPComplement_normalizer_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P)
    (hNP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer (P : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
        (((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))) := by
  classical
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hImage : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥((Subgroup.normalizer P).map f) :=
    hasNormalPComplement_subgroup_map f (Subgroup.normalizer P) hNP
  have hEq :
      Subgroup.normalizer ((P.map f : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (Subgroup.normalizer P).map f := by
    simpa [f] using
      OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
        hp_coprime hP_pgroup
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hImage

/-- If `N ⊴ G` is a normal `p'`-subgroup, then a normal `p`-complement in
`C_G(P)` pushes to a normal `p`-complement in `C_{G/N}(Pbar)`.

This combines subgroup-image inheritance with Isaacs Lemma 7.7(b). -/
theorem hasNormalPComplement_centralizer_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P)
    (hCP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer (P : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))) := by
  classical
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hImage : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥((Subgroup.centralizer (P : Set G)).map f) :=
    hasNormalPComplement_subgroup_map f (Subgroup.centralizer (P : Set G)) hCP
  have hEq :
      Subgroup.centralizer ((P.map f : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (Subgroup.centralizer (P : Set G)).map f := by
    simpa [f] using centralizer_map_of_coprime_kernel hp_coprime hP_pgroup
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hImage

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

/-- **Isaacs Theorem 7.1, Step 3 (center identification).**

If `N ⊴ G` is a normal `p′`-subgroup and `P` is a `p`-subgroup, then the ambient
image of `Z(P)` is carried to the ambient image of `Z(P̄)` under `G → G/N`.
The quotient map is injective on `P` because `P ∩ N = 1`; this is the center
analogue of `thompsonJ_map_of_coprime_kernel`. -/
theorem center_map_subtype_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    (Subgroup.center ↥(P.map (QuotientGroup.mk' N))).map
        (P.map (QuotientGroup.mk' N)).subtype =
      ((Subgroup.center ↥P).map P.subtype).map (QuotientGroup.mk' N) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : ↥P →* G ⧸ N := q.comp P.subtype
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  have hqP_inj : Function.Injective qP := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_N : (x : G) ∈ N := by
      have hx' : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
      rwa [QuotientGroup.ker_mk'] at hx'
    have hx_inf : (x : G) ∈ P ⊓ N := ⟨x.property, hx_N⟩
    rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
    exact Subtype.ext hx_inf
  apply center_map_subtype_map_of_restrict_injective
  simpa [qP, q] using hqP_inj

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

section MinimalCounterexampleStepTwo

/-- If one Sylow `p`-subgroup is trivial, the whole group is its own normal
`p`-complement. -/
theorem hasNormalPComplement_of_sylow_eq_bot
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : (P : Subgroup G) = ⊥) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine ⟨⊤, inferInstance, fun Q => ?_⟩
  have hQP : (Q : Subgroup G) = (P : Subgroup G) :=
    P.is_maximal' Q.isPGroup' (by rw [hP]; exact bot_le)
  rw [hQP, hP]
  exact Subgroup.isComplement'_top_bot

end MinimalCounterexampleStepTwo

section MinimalCounterexampleStepThree

/-- **Isaacs Theorem 7.1, Step 3.**

In a minimal counterexample, the normal `p′`-core is trivial.  If it were
nontrivial, Lemma 7.7 and the quotient formulas for `Z(P)` and `J(P)` would
transport both local normal-complement hypotheses to the smaller quotient.
Minimality gives a normal `p`-complement there, and the preceding lifting
theorem gives one in `G`, contradicting the counterexample assumption. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥ := by
  classical
  set N : Subgroup G :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G with hN_def
  have hN_normal : N.Normal := by
    dsimp [N]
    infer_instance
  have hN_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} N := by
    dsimp [N]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ≠ p}
  change N = ⊥
  by_contra hN_ne
  have hp_coprime : ¬ p ∣ Nat.card N := by
    intro hp
    have hp_mem : p ∈ (Nat.card N).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨Fact.out, hp, Nat.card_pos.ne'⟩
    exact (hN_pi' p hp_mem) rfl
  have hP_ne : (P : Subgroup G) ≠ ⊥ := by
    intro hP_bot
    exact hG (hasNormalPComplement_of_sylow_eq_bot P hP_bot)
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  set Pbar : Sylow p (G ⧸ N) := P.mapSurjective hq with hPbar_def
  have hPbar_coe :
      (Pbar : Subgroup (G ⧸ N)) = (P : Subgroup G).map q := by
    rw [hPbar_def, Sylow.coe_mapSurjective]
  have : Nontrivial ↥(P : Subgroup G) :=
    (P : Subgroup G).nontrivial_iff_ne_bot.mpr hP_ne
  set Z : Subgroup G :=
    (Subgroup.center ↥(P : Subgroup G)).map
      (P : Subgroup G).subtype with hZ_def
  have hZ_ne : Z ≠ ⊥ := by
    rw [hZ_def, Ne,
      Subgroup.map_eq_bot_iff_of_injective _
        (P : Subgroup G).subtype_injective]
    exact (Subgroup.center ↥(P : Subgroup G)).nontrivial_iff_ne_bot.mp
      P.isPGroup'.center_nontrivial
  have hZ_p : IsPGroup p Z := by
    rw [hZ_def]
    exact
      (P.isPGroup'.to_subgroup (Subgroup.center ↥(P : Subgroup G))).map
        (P : Subgroup G).subtype
  have hCenter :
      (Subgroup.center ↥(Pbar : Subgroup (G ⧸ N))).map
          (Pbar : Subgroup (G ⧸ N)).subtype =
        Z.map q := by
    rw [hPbar_coe]
    simpa only [hZ_def, q] using
      (center_map_subtype_map_of_coprime_kernel
        (G := G) (N := N) hp_coprime P.isPGroup')
  have hCZ_image :=
    hasNormalPComplement_centralizer_map_of_coprime_kernel
      (G := G) (N := N) hp_coprime hZ_p (hHyp P).1
  have hCZbar :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.centralizer
          (((Subgroup.center ↥(Pbar : Subgroup (G ⧸ N))).map
            (Pbar : Subgroup (G ⧸ N)).subtype :
              Subgroup (G ⧸ N)) : Set (G ⧸ N))) := by
    rw [hCenter]
    simpa only [q] using hCZ_image
  set J : Subgroup G :=
    Subgroup.thompsonJ (P : Subgroup G) p with hJ_def
  have hJ_ne : J ≠ ⊥ := by
    rw [hJ_def]
    exact Subgroup.thompsonJ_ne_bot P.isPGroup' hP_ne
  have hJ_p : IsPGroup p J := by
    rw [hJ_def]
    exact P.isPGroup'.to_le (Subgroup.thompsonJ_le (P : Subgroup G) p)
  have hJ_map :
      Subgroup.thompsonJ (Pbar : Subgroup (G ⧸ N)) p = J.map q := by
    rw [hPbar_coe]
    simpa only [hJ_def, q] using
      (thompsonJ_map_of_coprime_kernel
        (G := G) (N := N) hp_coprime P.isPGroup')
  have hNJ_image :=
    hasNormalPComplement_normalizer_map_of_coprime_kernel
      (G := G) (N := N) hp_coprime hJ_p (hHyp P).2
  have hNJbar :
      OddOrder.Isaacs.Ch05.HasNormalPComplement p
        ↥(Subgroup.normalizer
          ((Subgroup.thompsonJ (Pbar : Subgroup (G ⧸ N)) p :
            Subgroup (G ⧸ N)) : Set (G ⧸ N))) := by
    rw [hJ_map]
    simpa only [q] using hNJ_image
  have hPbar_local :
      HasThompsonLocalPComplements p (Pbar : Subgroup (G ⧸ N)) :=
    ⟨hCZbar, hNJbar⟩
  have hQ_hyp : HasThompsonPComplementHypothesis p (G ⧸ N) := by
    rw [hasThompsonPComplementHypothesis_iff Pbar]
    exact hPbar_local
  have hcard : Nat.card (G ⧸ N) < Nat.card G :=
    Subgroup.card_quotient_lt_of_ne_bot hN_ne
  have hQ_complement :=
    ih (G ⧸ N) hcard hQ_hyp
  exact hG
    (hasNormalPComplement_of_quotient_of_isPiGroup_compl
      hN_pi' hQ_complement)

end MinimalCounterexampleStepThree

end OddOrder.Isaacs.Ch07
