-- Prove2me | solution 1 for Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e98773ec-4e0c-5399-aeb6-fb793504ae0c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex

set_option autoImplicit false

namespace DoubleCosetFibre

open scoped Pointwise
open MulAction

variable {G : Type*} [Group G]

def stabH (H K : Subgroup G) (g : G) : Subgroup G := H ⊓ K.map (MulAut.conj g).toMonoidHom

theorem mem_stabH {H K : Subgroup G} {g h : G} : h ∈ stabH H K g ↔ h ∈ H ∧ g⁻¹ * h * g ∈ K := by
  unfold stabH
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hH, k, hk, rfl⟩
    refine ⟨hH, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
    exact hk
  · rintro ⟨hH, hk⟩
    refine ⟨hH, g⁻¹ * h * g, hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem stabH_mono {H K K' : Subgroup G} (hK : K' ≤ K) (g : G) : stabH H K' g ≤ stabH H K g := by
  intro h hh
  rw [mem_stabH] at hh ⊢
  exact ⟨hh.1, hK hh.2⟩

theorem stabH_mul (H K : Subgroup G) (g h k : G) (hh : h ∈ H) (hk : k ∈ K) :
    stabH H K (h * g * k) = (stabH H K g).map (MulAut.conj h).toMonoidHom := by
  ext y
  rw [mem_stabH, Subgroup.mem_map]
  constructor
  · rintro ⟨hyH, hyK⟩
    refine ⟨h⁻¹ * y * h, ?_, ?_⟩
    · rw [mem_stabH]
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hyH) hh, ?_⟩
      have : g⁻¹ * (h⁻¹ * y * h) * g = k * ((h * g * k)⁻¹ * y * (h * g * k)) * k⁻¹ := by group
      rw [this]
      exact K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨z, hz, rfl⟩
    rw [mem_stabH] at hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨H.mul_mem (H.mul_mem hh hz.1) (H.inv_mem hh), ?_⟩
    have : (h * g * k)⁻¹ * (h * z * h⁻¹) * (h * g * k) = k⁻¹ * (g⁻¹ * z * g) * k := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) hz.2) hk

theorem stabH_mul_right (H K : Subgroup G) (g k : G) (hk : k ∈ K) : stabH H K (g * k) = stabH H K g := by
  ext y
  rw [mem_stabH, mem_stabH]
  constructor
  · rintro ⟨hyH, hyK⟩
    refine ⟨hyH, ?_⟩
    have : g⁻¹ * y * g = k * ((g * k)⁻¹ * y * (g * k)) * k⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)
  · rintro ⟨hyH, hyK⟩
    refine ⟨hyH, ?_⟩
    have : (g * k)⁻¹ * y * (g * k) = k⁻¹ * (g⁻¹ * y * g) * k := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) hyK) hk

theorem relIndex_stabH_mul (H K K' : Subgroup G) (hK : K' ≤ K) (g h k : G) (hh : h ∈ H) (hk : k ∈ K') :
    (stabH H K' (h * g * k)).relIndex (stabH H K (h * g * k)) = (stabH H K' g).relIndex (stabH H K g) := by
  rw [stabH_mul H K' g h k hh hk, stabH_mul H K g h k hh (hK hk)]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

section PartOne

variable (H K K' : Subgroup G) (hK : K' ≤ K) (x : G)

include hK

omit hK in

abbrev Fibre : Type _ :=
  {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x}

omit hK in

def toK : stabH H K x →* K where
  toFun h := ⟨x⁻¹ * h * x, (mem_stabH.mp h.2).2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

omit hK in
scoped instance actY : MulAction (stabH H K x) (K ⧸ K'.subgroupOf K) :=
  MulAction.compHom _ (toK H K x)

omit hK in
theorem smul_mk (h : stabH H K x) (k : K) :
    h • (QuotientGroup.mk k : K ⧸ K'.subgroupOf K) = QuotientGroup.mk (toK H K x h * k) := rfl

def psi : K ⧸ K'.subgroupOf K → Fibre H K K' x :=
  Quotient.lift (fun k : K => (⟨DoubleCoset.mk H K' (x * k), by
      obtain ⟨h, k', hh, hk', he⟩ := (DoubleCoset.mk_out_eq_mul H K' (x * k))
      rw [he, DoubleCoset.eq]
      exact ⟨h⁻¹, H.inv_mem hh, ((k : G) * k')⁻¹, K.inv_mem (K.mul_mem k.2 (hK hk')), by group⟩⟩ : Fibre H K K' x))
    (by
      intro k₁ k₂ hrel
      apply Subtype.ext
      simp only
      rw [DoubleCoset.eq]
      have : (k₁⁻¹ * k₂ : K) ∈ K'.subgroupOf K := QuotientGroup.leftRel_apply.mp hrel
      rw [Subgroup.mem_subgroupOf] at this
      exact ⟨1, H.one_mem, k₁⁻¹ * k₂, this, by simp [mul_assoc]⟩)

theorem psi_mk (k : K) : (psi H K K' hK x (QuotientGroup.mk k) : Fibre H K K' x).1 = DoubleCoset.mk H K' (x * k) := rfl

theorem psi_surjective : Function.Surjective (psi H K K' hK x) := by
  rintro ⟨c, hc⟩
  have hout := DoubleCoset.out_eq' H K' c

  obtain ⟨h, hh, k, hk, he⟩ := (DoubleCoset.eq H K _ _).mp hc.symm

  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  apply Subtype.ext
  simp only [psi_mk]
  rw [← hout, DoubleCoset.eq]
  exact ⟨h, hh, 1, K'.one_mem, by rw [he]; group⟩

theorem psi_eq_psi_iff (k₁ k₂ : K) :
    psi H K K' hK x (QuotientGroup.mk k₁) = psi H K K' hK x (QuotientGroup.mk k₂) ↔
      ∃ h : stabH H K x, h • (QuotientGroup.mk k₁ : K ⧸ K'.subgroupOf K) = QuotientGroup.mk k₂ := by
  constructor
  · intro he
    have he' := congrArg Subtype.val he
    simp only [psi_mk] at he'
    rw [DoubleCoset.eq] at he'
    obtain ⟨h, hh, k', hk', he'⟩ := he'

    have hhx : h ∈ stabH H K x := by
      rw [mem_stabH]
      refine ⟨hh, ?_⟩
      have e3 : k' = (h * (x * k₁))⁻¹ * (x * k₂) := by rw [he']; group
      have : x⁻¹ * h * x = (k₂ : G) * k'⁻¹ * (k₁ : G)⁻¹ := by rw [e3]; group
      rw [this]
      exact K.mul_mem (K.mul_mem k₂.2 (K.inv_mem (hK hk'))) (K.inv_mem k₁.2)
    refine ⟨⟨h, hhx⟩, ?_⟩
    rw [smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((x⁻¹ * h * x * k₁ : G))⁻¹ * k₂ ∈ K'
    have e3 : k' = (h * (x * k₁))⁻¹ * (x * k₂) := by rw [he']; group
    have : ((x⁻¹ * h * x * k₁ : G))⁻¹ * k₂ = k' := by rw [e3]; group
    rw [this]; exact hk'
  · rintro ⟨h, hh⟩
    rw [← hh, smul_mk]
    apply Subtype.ext
    simp only [psi_mk]
    rw [DoubleCoset.eq]
    refine ⟨h, (mem_stabH.mp h.2).1, 1, K'.one_mem, ?_⟩
    show (x * (x⁻¹ * (h : G) * x * k₁) : G) = h * (x * k₁) * 1
    group

theorem psi_smul (h : stabH H K x) (y : K ⧸ K'.subgroupOf K) :
    psi H K K' hK x (h • y) = psi H K K' hK x y := by
  induction y using QuotientGroup.induction_on with
  | H k => exact ((psi_eq_psi_iff H K K' hK x k (toK H K x h * k)).mpr ⟨h, rfl⟩).symm

noncomputable def orbitEquiv : orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K) ≃ Fibre H K K' x :=
  Equiv.ofBijective
    (Quotient.lift (fun y => psi H K K' hK x y) (by
      intro y₁ y₂ hrel
      obtain ⟨h, rfl⟩ := hrel
      exact psi_smul H K K' hK x h y₂))
    ⟨by
      intro O₁ O₂ he
      induction O₁ using Quotient.inductionOn with
      | h y₁ =>
      induction O₂ using Quotient.inductionOn with
      | h y₂ =>
      induction y₁ using QuotientGroup.induction_on with
      | H k₁ =>
      induction y₂ using QuotientGroup.induction_on with
      | H k₂ =>
      obtain ⟨h, hh⟩ := (psi_eq_psi_iff H K K' hK x k₁ k₂).mp he
      exact Quotient.sound ⟨h⁻¹, by rw [← hh]; exact inv_smul_smul h _⟩,
     by
      intro c
      obtain ⟨y, rfl⟩ := psi_surjective H K K' hK x c
      exact ⟨Quotient.mk _ y, rfl⟩⟩

theorem stabilizer_eq (k : K) :
    (stabilizer (stabH H K x) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)).map (stabH H K x).subtype =
      stabH H K' (x * k) := by
  ext g
  rw [Subgroup.mem_map, mem_stabH]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_stabilizer_iff, smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hh
    have hh' := hh
    refine ⟨(mem_stabH.mp h.2).1, ?_⟩
    show (x * (k : G))⁻¹ * (h : G) * (x * k) ∈ K'

    have : (x * k : G)⁻¹ * h * (x * k) = (((toK H K x h * k : K) : G)⁻¹ * k)⁻¹ := by
      show (x * k : G)⁻¹ * h * (x * k) = ((x⁻¹ * h * x * k : G)⁻¹ * k)⁻¹
      group
    rw [this]
    exact K'.inv_mem hh'
  · rintro ⟨hgH, hgK'⟩
    have hgx : g ∈ stabH H K x := by
      rw [mem_stabH]
      refine ⟨hgH, ?_⟩
      have : x⁻¹ * g * x = (k : G) * ((x * k)⁻¹ * g * (x * k)) * (k : G)⁻¹ := by group
      rw [this]
      exact K.mul_mem (K.mul_mem k.2 (hK hgK')) (K.inv_mem k.2)
    refine ⟨⟨g, hgx⟩, ?_, rfl⟩
    rw [mem_stabilizer_iff, smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((x⁻¹ * g * x * k : G))⁻¹ * k ∈ K'
    have : ((x⁻¹ * g * x * k : G))⁻¹ * k = ((x * k)⁻¹ * g * (x * k))⁻¹ := by group
    rw [this]
    exact K'.inv_mem hgK'

theorem relIndex_eq_card_orbit (k : K) [Finite (K ⧸ K'.subgroupOf K)] :
    (stabH H K' (x * k)).relIndex (stabH H K x) =
      Nat.card (orbit (stabH H K x) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)) := by
  rw [Subgroup.relIndex, ← stabilizer_eq H K K' hK x k, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), index_stabilizer,
    ← Nat.card_coe_set_eq]

omit hK in

theorem card_eq_sum_card_orbits [Fintype (K ⧸ K'.subgroupOf K)]
    [Fintype (orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K))] :
    Fintype.card (K ⧸ K'.subgroupOf K) =
      ∑ O : orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K), Nat.card (orbit (stabH H K x) O.out) := by
  classical
  rw [Fintype.card_congr (selfEquivSigmaOrbits (stabH H K x) (K ⧸ K'.subgroupOf K)), Fintype.card_sigma]
  refine Finset.sum_congr rfl fun O _ => ?_
  rw [Nat.card_eq_fintype_card]

theorem sum_fibre_relIndex_stabH_eq_relIndex [K'.IsFiniteRelIndex K]
    [Fintype (Fibre H K K' x)] :
    ∑ c : Fibre H K K' x, (stabH H K' c.1.out).relIndex (stabH H K c.1.out) = K'.relIndex K := by
  classical
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K)) :=
    Fintype.ofEquiv _ (orbitEquiv H K K' hK x).symm

  rw [← Fintype.sum_equiv (orbitEquiv H K K' hK x)
    (fun O => Nat.card (orbit (stabH H K x) O.out))
    (fun c => (stabH H K' c.1.out).relIndex (stabH H K c.1.out)) ?_]
  · rw [← card_eq_sum_card_orbits H K K' x, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  · intro O
    induction O using Quotient.inductionOn with
    | h y =>
    induction y using QuotientGroup.induction_on with
    | H k =>
    show Nat.card (orbit (stabH H K x)
        (Quotient.mk (orbitRel (stabH H K x) (K ⧸ K'.subgroupOf K)) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)).out) =
      (stabH H K' (DoubleCoset.mk H K' (x * (k : G))).out).relIndex (stabH H K (DoubleCoset.mk H K' (x * (k : G))).out)
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : stabH H K x, h₀ • (QuotientGroup.mk k : K ⧸ K'.subgroupOf K) =
        (Quotient.mk (orbitRel (stabH H K x) (K ⧸ K'.subgroupOf K)) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)).out :=
      orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (stabH H K x) (K ⧸ K'.subgroupOf K))
        (QuotientGroup.mk k : K ⧸ K'.subgroupOf K))
    rw [← hh₀, orbit_smul, ← relIndex_eq_card_orbit H K K' hK x k]
    obtain ⟨h, k', hh, hk', he⟩ := DoubleCoset.mk_out_eq_mul H K' (x * k)
    rw [he, relIndex_stabH_mul H K K' hK (x * k) h k' hh hk', stabH_mul_right H K x k k.2]

end PartOne

theorem sum_filter_card_orbit_eq_card {M α : Type*} [Group M] [MulAction M α] [Fintype α]
    [Fintype (orbitRel.Quotient M α)] (A : Set α) [DecidablePred (· ∈ A)]
    (P : orbitRel.Quotient M α → Prop) [DecidablePred P]
    (hP : ∀ a : α, P (Quotient.mk (orbitRel M α) a) ↔ a ∈ A) :
    ∑ O ∈ Finset.univ.filter P, Nat.card (orbit M O.out) = Fintype.card A := by
  classical
  have hmaps : ∀ a ∈ Finset.univ.filter (fun a : α => a ∈ A),
      Quotient.mk (orbitRel M α) a ∈ Finset.univ.filter P := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (hP a).mpr ha
  rw [← Set.toFinset_card, show A.toFinset = Finset.univ.filter (fun a : α => a ∈ A) by ext a; simp,
    Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun O hO => ?_
  have hPO : P O := (Finset.mem_filter.mp hO).2

  have hfib : (Finset.univ.filter (fun a : α => a ∈ A)).filter (fun a => Quotient.mk (orbitRel M α) a = O) =
      (orbit M O.out).toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    constructor
    · rintro ⟨-, ha⟩
      have : Quotient.mk (orbitRel M α) a = Quotient.mk (orbitRel M α) O.out := by rw [ha, Quotient.out_eq]
      exact orbitRel_apply.mp (Quotient.exact this)
    · intro ha
      have hq : Quotient.mk (orbitRel M α) a = O := by
        rw [← Quotient.out_eq O]
        exact Quotient.sound (orbitRel_apply.mpr ha)
      refine ⟨?_, hq⟩
      exact (hP a).mp (hq ▸ hPO)
  rw [hfib, Set.toFinset_card, Nat.card_eq_fintype_card]

section Harmonic

variable (H K K₁ K₂ K₁₂ : Subgroup G) (hK₁ : K₁ ≤ K) (hK₂ : K₂ ≤ K)
  (h₁ : K₁₂ ≤ K₁) (h₂ : K₁₂ ≤ K₂) (hinf : K₁ ⊓ K₂ ≤ K₁₂)
  (hsurj : ∀ k : K, ∃ k₁ : K₁, ((k₁ : G)⁻¹ * k) ∈ K₂) (z : G)

def theta : K₁ ⧸ K₁₂.subgroupOf K₁ → K ⧸ K₂.subgroupOf K :=
  Quotient.map' (fun k₁ : K₁ => (⟨(k₁ : G), hK₁ k₁.2⟩ : K)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    exact h₂ hab)

theorem theta_mk (k₁ : K₁) :
    theta K K₁ K₂ K₁₂ hK₁ h₂ (QuotientGroup.mk k₁) = QuotientGroup.mk (⟨(k₁ : G), hK₁ k₁.2⟩ : K) := rfl

include hsurj hinf in
theorem theta_bijective : Function.Bijective (theta K K₁ K₂ K₁₂ hK₁ h₂) := by
  constructor
  · intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [theta_mk, theta_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hinf (Subgroup.mem_inf.mpr ⟨K₁.mul_mem (K₁.inv_mem a.2) b.2, hab⟩)
  · intro c
    induction c using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨k₁, hk₁⟩ := hsurj k
    refine ⟨QuotientGroup.mk k₁, ?_⟩
    rw [theta_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hk₁

theorem theta_smul (h : stabH H K₁ z) (a : K₁ ⧸ K₁₂.subgroupOf K₁) :
    theta K K₁ K₂ K₁₂ hK₁ h₂ (h • a) = (Subgroup.inclusion (stabH_mono (H := H) hK₁ z) h) • theta K K₁ K₂ K₁₂ hK₁ h₂ a := by
  induction a using QuotientGroup.induction_on with
  | H k₁ =>
  rw [smul_mk, theta_mk, theta_mk, smul_mk]
  rfl

variable (y : G) (hyz : DoubleCoset.mk H K z = DoubleCoset.mk H K y)

abbrev Fibre₂ : Type _ :=
  {c : DoubleCoset.Quotient (H : Set G) (K₁₂ : Set G) //
    DoubleCoset.mk H K₂ c.out = DoubleCoset.mk H K₂ y ∧ DoubleCoset.mk H K₁ c.out = DoubleCoset.mk H K₁ z}

include hK₁ hK₂ h₁ h₂ hinf hyz hsurj in

theorem sum_fibre₂_relIndex_stabH_eq [K₂.IsFiniteRelIndex K] [K₁₂.IsFiniteRelIndex K₁]
    [Fintype (Fibre₂ H K₁ K₂ K₁₂ z y)] :
    ∑ c : Fibre₂ H K₁ K₂ K₁₂ z y, (stabH H K₁₂ c.1.out).relIndex (stabH H K₁ c.1.out) =
      (stabH H K₂ y).relIndex (stabH H K y) := by
  classical

  have hK₁₂le : K₁₂ ≤ K₁ := h₁
  haveI : Finite (K ⧸ K₂.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ K₂.subgroupOf K) := Fintype.ofFinite _
  haveI : Finite (K₁ ⧸ K₁₂.subgroupOf K₁) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K₁ ⧸ K₁₂.subgroupOf K₁) := Fintype.ofFinite _

  obtain ⟨h₀, hh₀, k₀, hk₀, hy⟩ := (DoubleCoset.eq H K z y).mp hyz
  set y₀ : K ⧸ K₂.subgroupOf K := QuotientGroup.mk ⟨k₀, hk₀⟩ with hy₀def
  let Ω : Set (K ⧸ K₂.subgroupOf K) := orbit (stabH H K z) y₀
  let A : Set (K₁ ⧸ K₁₂.subgroupOf K₁) := (theta K K₁ K₂ K₁₂ hK₁ h₂) ⁻¹' Ω

  have hcond : ∀ k₁ : K₁, DoubleCoset.mk H K₂ (z * k₁) = DoubleCoset.mk H K₂ y ↔
      theta K K₁ K₂ K₁₂ hK₁ h₂ (QuotientGroup.mk k₁) ∈ Ω := by
    intro k₁
    rw [theta_mk, hy]
    have e1 : DoubleCoset.mk H K₂ (h₀ * z * k₀) = DoubleCoset.mk H K₂ (z * k₀) := by
      rw [DoubleCoset.eq]; exact ⟨h₀⁻¹, H.inv_mem hh₀, 1, K₂.one_mem, by group⟩
    rw [e1]

    have key := psi_eq_psi_iff H K K₂ hK₂ z (⟨(k₁ : G), hK₁ k₁.2⟩ : K) ⟨k₀, hk₀⟩
    have e2 : ∀ k : K, ((psi H K K₂ hK₂ z (QuotientGroup.mk k) : Fibre H K K₂ z).1) = DoubleCoset.mk H K₂ (z * k) :=
      fun k => rfl
    constructor
    · intro hk
      have : psi H K K₂ hK₂ z (QuotientGroup.mk (⟨(k₁ : G), hK₁ k₁.2⟩ : K)) = psi H K K₂ hK₂ z (QuotientGroup.mk ⟨k₀, hk₀⟩) := by
        apply Subtype.ext; rw [e2, e2]; exact hk
      obtain ⟨h, hh⟩ := key.mp this
      exact mem_orbit_iff.mpr ⟨h⁻¹, by rw [hy₀def, ← hh, inv_smul_smul]⟩
    · intro hk
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp hk
      have : psi H K K₂ hK₂ z (QuotientGroup.mk (⟨(k₁ : G), hK₁ k₁.2⟩ : K)) = psi H K K₂ hK₂ z (QuotientGroup.mk ⟨k₀, hk₀⟩) :=
        key.mpr ⟨h⁻¹, by rw [← hh, inv_smul_smul]⟩
      have hv := congrArg Subtype.val this
      rw [e2, e2] at hv
      exact hv

  have hθbij := theta_bijective K K₁ K₂ K₁₂ hK₁ h₂ hinf hsurj
  have hAinv : ∀ (h : stabH H K₁ z) (a : K₁ ⧸ K₁₂.subgroupOf K₁), a ∈ A → h • a ∈ A := by
    intro h a ha
    show theta K K₁ K₂ K₁₂ hK₁ h₂ (h • a) ∈ Ω
    rw [theta_smul]
    exact mem_orbit_of_mem_orbit _ ha
  haveI : Fintype (orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) := Fintype.ofFinite _
  let P : orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁) → Prop := fun O => theta K K₁ K₂ K₁₂ hK₁ h₂ O.out ∈ Ω
  have hP : ∀ a, P (Quotient.mk (orbitRel (stabH H K₁ z) _) a) ↔ a ∈ A := by
    intro a
    show theta K K₁ K₂ K₁₂ hK₁ h₂ (Quotient.mk (orbitRel (stabH H K₁ z) _) a).out ∈ Ω ↔ theta K K₁ K₂ K₁₂ hK₁ h₂ a ∈ Ω
    obtain ⟨h, hh⟩ : ∃ h : stabH H K₁ z, h • a = (Quotient.mk (orbitRel (stabH H K₁ z) _) a).out :=
      orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) a)
    rw [← hh]
    constructor
    · intro h1
      have := hAinv h⁻¹ _ h1
      rwa [inv_smul_smul] at this
    · intro h1; exact hAinv h _ h1

  have hiff : ∀ O : orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁),
      P O ↔ (DoubleCoset.mk H K₂ ((orbitEquiv H K₁ K₁₂ hK₁₂le z O : Fibre H K₁ K₁₂ z).1.out) = DoubleCoset.mk H K₂ y) := by
    intro O
    induction O using Quotient.inductionOn with
    | h a =>
    induction a using QuotientGroup.induction_on with
    | H k₁ =>
    rw [hP]
    show theta K K₁ K₂ K₁₂ hK₁ h₂ (QuotientGroup.mk k₁) ∈ Ω ↔ _
    rw [← hcond k₁]

    have hval : ((orbitEquiv H K₁ K₁₂ hK₁₂le z (Quotient.mk _ (QuotientGroup.mk k₁))) : Fibre H K₁ K₁₂ z).1 =
        DoubleCoset.mk H K₁₂ (z * k₁) := rfl
    rw [hval]
    obtain ⟨h, k', hh, hk', he⟩ := DoubleCoset.mk_out_eq_mul H K₁₂ (z * k₁)
    rw [he]
    have : DoubleCoset.mk H K₂ (h * (z * ↑k₁) * k') = DoubleCoset.mk H K₂ (z * k₁) := by
      rw [DoubleCoset.eq]; exact ⟨h⁻¹, H.inv_mem hh, k'⁻¹, K₂.inv_mem (h₂ hk'), by group⟩
    rw [this]
  let eF : {O : orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁) // P O} ≃ Fibre₂ H K₁ K₂ K₁₂ z y :=
    (Equiv.subtypeEquiv (orbitEquiv H K₁ K₁₂ hK₁₂le z) hiff).trans
      { toFun := fun c => ⟨c.1.1, c.2, c.1.2⟩
        invFun := fun c => (⟨⟨c.1, c.2.2⟩, c.2.1⟩ :
          {b : Fibre H K₁ K₁₂ z // DoubleCoset.mk H K₂ b.1.out = DoubleCoset.mk H K₂ y})
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← Fintype.sum_equiv eF (fun O => Nat.card (orbit (stabH H K₁ z) O.1.out))
    (fun c => (stabH H K₁₂ c.1.out).relIndex (stabH H K₁ c.1.out)) ?_]
  swap
  ·
    rintro ⟨O, hO⟩
    induction O using Quotient.inductionOn with
    | h a =>
    induction a using QuotientGroup.induction_on with
    | H k =>
    show Nat.card (orbit (stabH H K₁ z)
        (Quotient.mk (orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁)).out) =
      (stabH H K₁₂ (DoubleCoset.mk H K₁₂ (z * (k : G))).out).relIndex (stabH H K₁ (DoubleCoset.mk H K₁₂ (z * (k : G))).out)
    obtain ⟨h₁, hh₁⟩ : ∃ h₁ : stabH H K₁ z, h₁ • (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁) =
        (Quotient.mk (orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁)).out :=
      orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁))
        (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁))
    rw [← hh₁, orbit_smul, ← relIndex_eq_card_orbit H K₁ K₁₂ hK₁₂le z k]
    obtain ⟨h, k', hh, hk', he⟩ := DoubleCoset.mk_out_eq_mul H K₁₂ (z * k)
    rw [he, relIndex_stabH_mul H K₁ K₁₂ hK₁₂le (z * k) h k' hh hk', stabH_mul_right H K₁ z k k.2]

  rw [show (∑ O : {O // P O}, Nat.card (orbit (stabH H K₁ z) O.1.out)) =
      ∑ O ∈ Finset.univ.filter P, Nat.card (orbit (stabH H K₁ z) O.out) from
    (Finset.sum_subtype (Finset.univ.filter P) (fun O => by simp) (fun O => Nat.card (orbit (stabH H K₁ z) O.out))).symm]
  rw [sum_filter_card_orbit_eq_card A P hP]

  have eAΩ : A ≃ Ω := Equiv.subtypeEquiv (Equiv.ofBijective _ hθbij) (fun a => Iff.rfl)
  rw [Fintype.card_congr eAΩ, ← Nat.card_eq_fintype_card]

  show Nat.card (orbit (stabH H K z) (QuotientGroup.mk (⟨k₀, hk₀⟩ : K) : K ⧸ K₂.subgroupOf K)) = _
  rw [← relIndex_eq_card_orbit H K K₂ hK₂ z ⟨k₀, hk₀⟩, hy,
    show h₀ * z * k₀ = h₀ * (z * k₀) * 1 by group,
    relIndex_stabH_mul H K K₂ hK₂ (z * k₀) h₀ 1 hh₀ K₂.one_mem, stabH_mul_right H K z k₀ hk₀]

end Harmonic

end DoubleCosetFibre
p2m_reactivate "P2MW.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex.DoubleCosetFibre"

open MulAction in
theorem solution
    {G : Type*} [Group G] (H K K' : Subgroup G) (hK : K' ≤ K) (x : G) [K'.IsFiniteRelIndex K]
    [Fintype {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x}] :
    ∑ c : {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x},
      (H ⊓ K'.map (MulAut.conj c.1.out).toMonoidHom).relIndex (H ⊓ K.map (MulAut.conj c.1.out).toMonoidHom) =
        K'.relIndex K :=
  DoubleCosetFibre.sum_fibre_relIndex_stabH_eq_relIndex H K K' hK x

end S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
end P2MW
export P2MW.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex (solution)
