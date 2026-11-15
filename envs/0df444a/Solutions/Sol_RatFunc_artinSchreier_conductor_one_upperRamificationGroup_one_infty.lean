-- Prove2me | solution 1 for RatFunc.artinSchreier_conductor_one_upperRamificationGroup_one_infty
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T11:40:46.03122+00:00
-- url     : https://prove2.me/submissions/85fca274-d3b6-4ad1-bbaf-cf7b47052b0e

import Mathlib
import Definitions.Def_RPLib_S4_SwanSlope1b

set_option autoImplicit false
set_option linter.unusedSectionVars false

open RamanujanPetersson IsDedekindDomain

namespace Slope1Sol

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

/-- The trivial-chart cover of a finite Galois field extension. -/
noncomputable abbrev fieldCover (K E : Type) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [IsGalois K E] : GalCover K where
  B := E
  G := E ≃ₐ[K] E
  inj := (faithfulSMul_iff_algebraMap_injective K E).2 (algebraMap K E).injective
  gal := inferInstance
  unramified := fun Q hQ => by
    have : Q = ⊥ := by
      rcases Ideal.eq_bot_or_top Q with h | h
      · exact h
      · exact absurd h hQ.ne_top
    subst this
    exact GalCover.inertia_bot_eq_bot

instance sdc (K E : Type) [Field K] [Field E] [Algebra K E] : SMulDistribClass (E ≃ₐ[K] E) E E :=
  ⟨fun g b x => by simp only [smul_eq_mul, AlgEquiv.smul_def, map_mul]⟩

section Bridge

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
  {L' : Type} [Field L'] [Algebra (RatFunc Fq) L'] [FiniteDimensional (RatFunc Fq) L']
  [IsGalois (RatFunc Fq) L']

attribute [local instance] GalCover.infChartAction

theorem coe_smul_chart (σ : L' ≃ₐ[RatFunc Fq] L') (b : GalCover.infChart Fq L') :
    (((σ : (fieldCover (RatFunc Fq) L').G) • b : GalCover.infChart Fq L') : L') = σ (b : L') := rfl

theorem mem_infInertia_iff (Q : HeightOneSpectrum (GalCover.infChart Fq L')) (σ : L' ≃ₐ[RatFunc Fq] L') :
    σ ∈ (fieldCover (RatFunc Fq) L').infInertia Fq L' Q.asIdeal ↔
      ∀ b : GalCover.infChart Fq L', ∃ c ∈ Q.asIdeal, (c : L') = σ b - b := by
  show (∀ x : GalCover.infChart Fq L', (σ : (fieldCover (RatFunc Fq) L').G) • x - x ∈ Q.asIdeal) ↔ _
  constructor
  · intro h b
    exact ⟨_, h b, rfl⟩
  · intro h b
    obtain ⟨c, hc, hce⟩ := h b
    have : (σ : (fieldCover (RatFunc Fq) L').G) • b - b = c := Subtype.ext (by rw [hce]; rfl)
    rw [this]
    exact hc

theorem exists_unif (Q : HeightOneSpectrum (GalCover.infChart Fq L')) :
    ∃ r : GalCover.infChart Fq L', Swan.adicAdd Q (algebraMap (GalCover.infChart Fq L') L' r) = 1 := by
  obtain ⟨r, hr1, hr2⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow Q.ne_bot 1)
  refine ⟨r, ?_⟩
  rw [pow_one] at hr1
  have h1 := (Swan.natCast_le_adicAdd_algebraMap_iff (L := L') Q r 1).2 (by rw [pow_one]; exact hr1)
  have h2 : ¬ ((2 : ℕ) : WithTop ℤ) ≤ Swan.adicAdd Q (algebraMap (GalCover.infChart Fq L') L' r) :=
    fun h => hr2 ((Swan.natCast_le_adicAdd_algebraMap_iff (L := L') Q r 2).1 h)
  generalize Swan.adicAdd Q (algebraMap (GalCover.infChart Fq L') L' r) = w at h1 h2
  induction w using WithTop.recTopCoe with
  | top => exact absurd le_top h2
  | coe m =>
    have h1' : (1 : ℤ) ≤ m := by exact_mod_cast h1
    have h2' : ¬ (2 : ℤ) ≤ m := fun h => h2 (by
      have h3 : ((2 : ℤ) : WithTop ℤ) ≤ (m : WithTop ℤ) := WithTop.coe_le_coe.2 h
      calc ((2 : ℕ) : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) := rfl
        _ ≤ _ := h3)
    have : m = 1 := by omega
    rw [this]; rfl

/-- The inertia group at `Q` (lib object). -/
noncomputable abbrev II (Q : HeightOneSpectrum (GalCover.infChart Fq L')) :
    Subgroup (L' ≃ₐ[RatFunc Fq] L') :=
  (fieldCover (RatFunc Fq) L').infInertia Fq L' Q.asIdeal

noncomputable instance fintypeII (Q : HeightOneSpectrum (GalCover.infChart Fq L')) : Fintype (II Q) :=
  GalCover.infInertia_fintype (fieldCover (RatFunc Fq) L') Fq L' Q

/-- The ramification function at `Q` (lib object). -/
noncomputable abbrev RR (Q : HeightOneSpectrum (GalCover.infChart Fq L')) : Swan.RamFn (II Q) :=
  (fieldCover (RatFunc Fq) L').infRamFn Fq L' Q

variable (Q : HeightOneSpectrum (GalCover.infChart Fq L')) (G : ℕ → Subgroup (L' ≃ₐ[RatFunc Fq] L'))
  (hG : ∀ (i : ℕ) (σ : L' ≃ₐ[RatFunc Fq] L'), σ ∈ G i ↔
      ∀ b : GalCover.infChart Fq L', ∃ c ∈ Q.asIdeal ^ (i + 1), (c : L') = σ b - b)

include hG in
theorem G_le_inertia (u : ℕ) : G u ≤ II Q := by
  intro σ hσ
  rw [II, mem_infInertia_iff]
  intro b
  obtain ⟨c, hc, hce⟩ := (hG u σ).1 hσ b
  exact ⟨c, Ideal.pow_le_self (Nat.succ_ne_zero u) hc, hce⟩

include hG in
theorem mem_lower_iff' (u : ℕ) (τ : II Q) :
    τ ∈ (RR Q).lower u ↔ (τ : L' ≃ₐ[RatFunc Fq] L') ∈ G u := by
  obtain ⟨r, hr⟩ := exists_unif Q
  have hv : ((fieldCover (RatFunc Fq) L').infLocData Fq L' Q).v
      (algebraMap (GalCover.infChart Fq L') L' r) = 1 := hr
  have key := ((fieldCover (RatFunc Fq) L').infLocData Fq L' Q).ramFn_i_of_unif hv τ
  rw [Swan.RamFn.mem_lower]
  change ((u + 1 : ℕ) : ℕ∞) ≤ ((fieldCover (RatFunc Fq) L').infLocData Fq L' Q).ramFn.i τ ↔ _
  rw [key]
  constructor
  · intro h
    rw [hG]
    intro b
    have h1 := Swan.LocData.le_of_natCast_le_toENat (Nat.le_add_left 1 u) h
    have h2 := ((fieldCover (RatFunc Fq) L').infLocData Fq L' Q).lb_bot hv τ
      (x := algebraMap (GalCover.infChart Fq L') L' b) (Swan.adicAdd_algebraMap_nonneg Q b)
    refine ⟨(τ : (fieldCover (RatFunc Fq) L').G) • b - b, ?_, rfl⟩
    rw [← Swan.natCast_le_adicAdd_algebraMap_iff (L := L')]
    exact le_trans h1 h2
  · intro h
    obtain ⟨c, hc, hce⟩ := (hG u τ).1 h r
    have h1 := (Swan.natCast_le_adicAdd_algebraMap_iff (L := L') Q c (u + 1)).2 hc
    apply Swan.LocData.natCast_le_toENat
    have h3 : algebraMap (GalCover.infChart Fq L') L' c =
        τ • algebraMap (GalCover.infChart Fq L') L' r - algebraMap (GalCover.infChart Fq L') L' r := hce
    rw [← h3]
    exact h1

include hG in
theorem map_lower (u : ℕ) : ((RR Q).lower u).map (II Q).subtype = G u := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (mem_lower_iff' Q G hG u τ).1 hτ
  · intro hσ
    exact ⟨⟨σ, G_le_inertia Q G hG u hσ⟩, (mem_lower_iff' Q G hG u _).2 hσ, rfl⟩

include hG in
theorem card_lower (u : ℕ) : Nat.card ((RR Q).lower u) = Nat.card (G u) := by
  rw [← map_lower Q G hG u, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

include hG in
theorem card_inertia : Nat.card (II Q) = Nat.card (G 0) := by
  rw [← card_lower Q G hG 0, Swan.RamFn.lower_zero, Subgroup.card_top]

include hG in
theorem phi_eq (m : ℕ) :
    (RR Q).phi m = ∑ u ∈ Finset.range m, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0) := by
  rw [Swan.RamFn.phi_eq_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [card_lower Q G hG, card_inertia Q G hG]

include hG in
theorem upperIdx_eq (v : ℚ) : (RR Q).upperIdx v =
    sInf {m : ℕ | v ≤ ∑ u ∈ Finset.range m, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0)} := by
  have hne : {m : ℕ | v ≤ ∑ u ∈ Finset.range m,
      (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0)}.Nonempty := by
    obtain ⟨m, hm⟩ := (RR Q).exists_le_phi v
    exact ⟨m, by rw [Set.mem_setOf_eq, ← phi_eq Q G hG]; exact hm⟩
  apply le_antisymm
  · rw [Swan.RamFn.upperIdx_le_iff, phi_eq Q G hG]
    exact Nat.sInf_mem hne
  · apply Nat.sInf_le
    rw [Set.mem_setOf_eq, ← phi_eq Q G hG]
    exact ((RR Q).upperIdx_le_iff v _).1 le_rfl

variable (Gu : ℚ → Subgroup (L' ≃ₐ[RatFunc Fq] L'))
  (hGu : ∀ v : ℚ, 0 < v → Gu v = G (sInf {m : ℕ |
      v ≤ ∑ u ∈ Finset.range m, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0)}))

include hG hGu in
theorem Gu_eq {v : ℚ} (hv : 0 < v) : Gu v = ((RR Q).upper v).map (II Q).subtype := by
  rw [hGu v hv, ← upperIdx_eq Q G hG, Swan.RamFn.upper, map_lower Q G hG]

include hG hGu in
theorem mem_Gu_iff {v : ℚ} (hv : 0 < v) (τ : II Q) :
    (τ : L' ≃ₐ[RatFunc Fq] L') ∈ Gu v ↔ τ ∈ (RR Q).upper v := by
  rw [Gu_eq Q G hG Gu hGu hv]
  exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)

include hG hGu in
theorem Gu_le_inertia {v : ℚ} (hv : 0 < v) : Gu v ≤ II Q := by
  rw [Gu_eq Q G hG Gu hGu hv]
  exact Subgroup.map_subtype_le ((RR Q).upper v)

end Bridge

section Sub

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
  {L' : Type} [Field L'] [Algebra (RatFunc Fq) L'] [FiniteDimensional (RatFunc Fq) L']
  [IsGalois (RatFunc Fq) L']

theorem normal_adj (g : RatFunc Fq) (y : L')
    (hy : y ^ Fintype.card Fq - y = algebraMap (RatFunc Fq) L' g) :
    Normal (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) := by
  rw [IntermediateField.normal_iff_forall_map_le]
  intro σ
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff]
  letI : Algebra Fq L' := ((algebraMap (RatFunc Fq) L').comp (algebraMap Fq (RatFunc Fq))).toAlgebra
  have h1 : y ^ Fintype.card Fq = y + algebraMap (RatFunc Fq) L' g := by rw [← hy]; ring
  have hz : (σ y - y) ^ Fintype.card Fq = σ y - y := by
    rw [GalCover.sub_pow_card_Fq Fq, ← map_pow, h1, map_add, AlgHom.commutes]; ring
  obtain ⟨c, hc⟩ := ArtinSchreier.exists_algebraMap_eq_of_pow_card Fq hz
  have hc' : algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) c) = σ y - y := hc
  have : σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) c) := by rw [hc']; ring
  rw [this]
  exact add_mem (IntermediateField.mem_adjoin_simple_self _ y) (IntermediateField.algebraMap_mem _ _)

theorem isGalois_adj (g : RatFunc Fq) (y : L')
    (hy : y ^ Fintype.card Fq - y = algebraMap (RatFunc Fq) L' g) :
    IsGalois (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) := by
  haveI := normal_adj g y hy
  haveI : Algebra.IsSeparable (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) :=
    Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc Fq)
      (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) L'
  exact ⟨⟩

variable (y : L') [IsGalois (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))]

/-- The tower `K(y) ⊆ L'` as a morphism of trivial-chart covers. -/
noncomputable def cHom : GalCover.CoverHom
    (fieldCover (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')))
    (fieldCover (RatFunc Fq) L') where
  ringHom := (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')).val
  grpHom := AlgEquiv.restrictNormalHom (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))
  surj := AlgEquiv.restrictNormalHom_surjective
    (K₁ := IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) L'
  equivariant := fun σ b =>
    AlgEquiv.restrictNormal_commutes σ (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) b

theorem asGen (g : RatFunc Fq) (hg : g.intDegree = 1)
    (hy : y ^ Fintype.card Fq - y = algebraMap (RatFunc Fq) L' g) :
    (fieldCover (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))).IsASGen Fq
      (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))
      (IntermediateField.AdjoinSimple.gen (RatFunc Fq) y) (-g) 1 where
  eq := by
    apply (algebraMap (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) L').injective
    rw [map_pow, map_sub, ← IsScalarTower.algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen,
      map_neg, sub_neg_eq_add, ← hy]
    ring
  ne_zero := fun h0 => by
    rw [neg_eq_zero] at h0
    rw [h0, RatFunc.intDegree_zero] at hg
    exact absurd hg (by norm_num)
  deg := by rw [RatFunc.intDegree_neg, hg]; norm_num
  one_le := le_rfl
  coprime := Nat.coprime_one_left _
  gen := fun σ hσ => by
    have hint : IsIntegral (RatFunc Fq) y := Algebra.IsIntegral.isIntegral y
    apply AlgEquiv.coe_algHom_injective
    apply (IntermediateField.adjoin.powerBasis hint).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen]
    exact hσ

variable {y}

theorem val_eq {g : RatFunc Fq}
    (h : (fieldCover (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))).IsASGen Fq
      (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))
      (IntermediateField.AdjoinSimple.gen (RatFunc Fq) y) (-g) 1) (σ : L' ≃ₐ[RatFunc Fq] L') :
    σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) (h.val ((cHom y).grpHom σ))) := by
  have h1 := congrArg (algebraMap (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) L')
    (h.val_spec ((cHom y).grpHom σ))
  rw [map_add, ← IsScalarTower.algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen] at h1
  have h2 : algebraMap (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) L'
      ((cHom y).grpHom σ • IntermediateField.AdjoinSimple.gen (RatFunc Fq) y) = σ y := by
    have := AlgEquiv.restrictNormal_commutes σ (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))
      (IntermediateField.AdjoinSimple.gen (RatFunc Fq) y)
    rw [IntermediateField.AdjoinSimple.algebraMap_gen] at this
    exact this
  rw [← h2, h1]

theorem val_eq_of {g : RatFunc Fq}
    (h : (fieldCover (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))).IsASGen Fq
      (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))
      (IntermediateField.AdjoinSimple.gen (RatFunc Fq) y) (-g) 1) (σ : L' ≃ₐ[RatFunc Fq] L') (a : Fq)
    (hσ : σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a)) :
    h.val ((cHom y).grpHom σ) = a := by
  have := (val_eq h σ).symm.trans hσ
  exact ((algebraMap (RatFunc Fq) L').injective.comp (algebraMap Fq (RatFunc Fq)).injective)
    (add_left_cancel this)

end Sub

end Slope1Sol

open scoped Classical

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq]
    (L' : Type) [Field L'] [Algebra (RatFunc Fq) L'] [FiniteDimensional (RatFunc Fq) L']
    [IsGalois (RatFunc Fq) L']
    (g : RatFunc Fq) (hg : g.intDegree = 1) (y : L')
    (hy : y ^ Fintype.card Fq - y = algebraMap (RatFunc Fq) L' g)
    (Q' : Ideal (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L')) [Q'.IsPrime]
    (hQ' : Q' ≠ ⊥)
    (hdeg : Nat.card (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L' ⧸ Q') =
      Fintype.card Fq)
    (G : ℕ → Subgroup (L' ≃ₐ[RatFunc Fq] L'))
    (hG : ∀ (i : ℕ) (σ : L' ≃ₐ[RatFunc Fq] L'), σ ∈ G i ↔
      ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L',
        ∃ c ∈ Q' ^ (i + 1), (c : L') = σ b - b)
    (Gu : ℚ → Subgroup (L' ≃ₐ[RatFunc Fq] L'))
    (hGu : ∀ v : ℚ, 0 < v → Gu v = G (sInf {m : ℕ |
      v ≤ ∑ u ∈ Finset.range m, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0)})) :
    (∀ a : Fq, ∃ σ ∈ Gu 1, σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a)) ∧
    (∀ v : ℚ, 1 < v → ∀ σ ∈ Gu v, σ y = y) ∧
    (∀ σ ∈ Gu 1, σ y = y → ∃ v : ℚ, 1 < v ∧ σ ∈ Gu v) ∧
    (∀ {k : Type} [Field k] (χ : Gu 1 →* kˣ),
      (∀ σ : Gu 1, (∃ v : ℚ, 1 < v ∧ (σ : L' ≃ₐ[RatFunc Fq] L') ∈ Gu v) → χ σ = 1) →
      ∃ ψ' : AddChar Fq k, ∀ (σ : Gu 1) (a : Fq),
        (σ : L' ≃ₐ[RatFunc Fq] L') y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a) →
          ((χ σ : kˣ) : k) = ψ' a) ∧
    (∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
      (ρ : Representation k (L' ≃ₐ[RatFunc Fq] L') V),
      (∀ v : ℚ, 1 < v → ∀ σ ∈ Gu v, ρ σ = LinearMap.id) →
      ∀ ψ : AddChar Fq k, ψ.IsPrimitive → (Fintype.card Fq : k) ≠ 0 →
      ∃ b : Fq, ∀ ρ' : Representation k (L' ≃ₐ[RatFunc Fq] L') V,
        (∀ (σ : L' ≃ₐ[RatFunc Fq] L') (a : Fq),
          σ y = y + algebraMap (RatFunc Fq) L' (algebraMap Fq (RatFunc Fq) a) → ρ' σ = ψ (b * a) • ρ σ) →
        ∑ᶠ u : ℕ, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0) *
          ((Module.finrank k V - Module.finrank k (Representation.invariants (ρ'.comp (G (u + 1)).subtype)) : ℕ) : ℚ) <
          Module.finrank k V) := by
  obtain ⟨Qh, rfl⟩ : ∃ Qh : HeightOneSpectrum (GalCover.infChart Fq L'), Qh.asIdeal = Q' :=
    ⟨⟨Q', inferInstance, hQ'⟩, rfl⟩
  have hG' : ∀ (i : ℕ) (σ : L' ≃ₐ[RatFunc Fq] L'), σ ∈ G i ↔
      ∀ b : GalCover.infChart Fq L', ∃ c ∈ Qh.asIdeal ^ (i + 1), (c : L') = σ b - b := hG
  have hdeg' : Nat.card (GalCover.infChart Fq L' ⧸ Qh.asIdeal) ≤ Nat.card Fq := by
    have := hdeg
    rw [← Nat.card_eq_fintype_card] at this
    exact this.le
  haveI : IsGalois (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) :=
    Slope1Sol.isGalois_adj g y hy
  have h := Slope1Sol.asGen y g hg hy
  have hf : ∀ b : (Slope1Sol.fieldCover (RatFunc Fq)
      (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))).B,
      algebraMap (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) L'
        (algebraMap (Slope1Sol.fieldCover (RatFunc Fq)
          (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L'))).B
          (IntermediateField.adjoin (RatFunc Fq) ({y} : Set L')) b) =
      algebraMap (Slope1Sol.fieldCover (RatFunc Fq) L').B L' ((Slope1Sol.cHom y).ringHom b) :=
    fun _ => rfl
  have hval0 : ∀ τ : Slope1Sol.II Qh, GalCover.s1Phi (Slope1Sol.cHom y) Fq h Qh τ = 1 →
      h.val ((Slope1Sol.cHom y).grpHom (τ : L' ≃ₐ[RatFunc Fq] L')) = 0 := by
    intro τ hτ
    rw [GalCover.s1Phi_apply] at hτ
    have := congrArg Multiplicative.toAdd hτ
    simpa using this
  have hW : ∀ τ : Slope1Sol.II Qh, τ ∈ (Slope1Sol.RR Qh).upper 1 →
      h.val ((Slope1Sol.cHom y).grpHom (τ : L' ≃ₐ[RatFunc Fq] L')) = 0 →
      ∃ v : ℚ, 1 < v ∧ (τ : L' ≃ₐ[RatFunc Fq] L') ∈ Gu v := by
    intro τ hτU hτ0
    have hΦ : GalCover.s1Phi (Slope1Sol.cHom y) Fq h Qh τ = 1 := by
      rw [GalCover.s1Phi_apply, hτ0]; rfl
    have hτW := GalCover.slope1_ker (Slope1Sol.cHom y) Fq hf h Qh hdeg' hτU hΦ
    have h1 := GalCover.one_lt_phi_s1 (Slope1Sol.fieldCover (RatFunc Fq) L') Fq Qh
    refine ⟨_, h1, (Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu (by linarith) τ).2 ?_⟩
    rw [← GalCover.s1W_eq_upper]
    exact hτW
  refine ⟨fun a => ?_, fun v hv σ hσ => ?_, fun σ hσ hσy => ?_, fun {k} _ χ hχ => ?_,
    fun {k V} _ _ _ _ _ ρ hρ ψ hψ hq => ?_⟩
  · -- (a)
    obtain ⟨τ, hτ, hτa⟩ := GalCover.slope1_surj (Slope1Sol.cHom y) Fq hf h Qh a
    refine ⟨τ, (Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu one_pos τ).2 hτ, ?_⟩
    rw [GalCover.s1Phi_apply] at hτa
    rw [Slope1Sol.val_eq h, Multiplicative.ofAdd.injective hτa]
  · -- (b)
    have hv0 : (0 : ℚ) < v := by linarith
    have hτ := (Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu hv0
      ⟨σ, Slope1Sol.Gu_le_inertia Qh G hG' Gu hGu hv0 hσ⟩).1 hσ
    have h0 := hval0 _ (GalCover.slope1_upper (Slope1Sol.cHom y) Fq hf h Qh hv hτ)
    rw [Slope1Sol.val_eq h σ]
    rw [show h.val ((Slope1Sol.cHom y).grpHom σ) = 0 from h0, map_zero, map_zero, add_zero]
  · -- (c)
    have hτ := (Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu one_pos
      ⟨σ, Slope1Sol.Gu_le_inertia Qh G hG' Gu hGu one_pos hσ⟩).1 hσ
    exact hW _ hτ (Slope1Sol.val_eq_of h σ 0 (by rw [map_zero, map_zero, add_zero]; exact hσy))
  · -- (d)
    have hle := Slope1Sol.Gu_le_inertia Qh G hG' Gu hGu (v := 1) one_pos
    let Φ' : Gu 1 →* Multiplicative Fq :=
      (GalCover.s1Phi (Slope1Sol.cHom y) Fq h Qh).comp (Subgroup.inclusion hle)
    have hsurj : Function.Surjective Φ' := by
      intro c
      obtain ⟨τ, hτ, hτc⟩ := GalCover.slope1_surj (Slope1Sol.cHom y) Fq hf h Qh (Multiplicative.toAdd c)
      refine ⟨⟨τ, (Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu one_pos τ).2 hτ⟩, ?_⟩
      exact hτc
    have hker : Φ'.ker ≤ χ.ker := by
      intro σ hσ
      rw [MonoidHom.mem_ker] at hσ ⊢
      apply hχ σ
      have hτU := (Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu one_pos (Subgroup.inclusion hle σ)).1 σ.2
      exact hW _ hτU (hval0 _ hσ)
    let χb := (MonoidHom.liftOfRightInverse Φ' (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj)) ⟨χ, hker⟩
    refine ⟨AddChar.toMonoidHomEquiv.symm ((Units.coeHom k).comp χb), fun σ a hσa => ?_⟩
    have hΦ : Φ' σ = Multiplicative.ofAdd a := by
      show GalCover.s1Phi (Slope1Sol.cHom y) Fq h Qh (Subgroup.inclusion hle σ) = _
      rw [GalCover.s1Phi_apply]
      exact congrArg Multiplicative.ofAdd (Slope1Sol.val_eq_of h σ a hσa)
    have := MonoidHom.liftOfRightInverse_comp_apply Φ' (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨χ, hker⟩ σ
    rw [hΦ] at this
    show ((χ σ : kˣ) : k) = ((χb (Multiplicative.ofAdd a) : kˣ) : k)
    rw [← this]
  · -- (e)
    have hB : (Slope1Sol.RR Qh).BrkLE (ρ.comp (Slope1Sol.II Qh).subtype) 1 := by
      intro v hv
      rw [eq_top_iff]
      intro w _
      rw [Swan.mem_fixd]
      intro τ hτ
      have h1 := hρ v hv τ ((Slope1Sol.mem_Gu_iff Qh G hG' Gu hGu (by linarith) τ).2 hτ)
      show ρ τ w = w
      rw [h1]
      rfl
    obtain ⟨b, hb⟩ := GalCover.slope1_swan (Slope1Sol.cHom y) Fq hf h Qh ρ hdeg' hB ψ hψ hq
    refine ⟨b, fun ρ' hρ' => ?_⟩
    have hρ'eq : ρ' = Swan.twist ρ ((h.lpsi (ψ.mulShift b)).comp (Slope1Sol.cHom y).grpHom) := by
      refine MonoidHom.ext fun σ => ?_
      rw [hρ' σ _ (Slope1Sol.val_eq h σ), Swan.twist_apply, MonoidHom.comp_apply, h.lpsi_apply,
        AddChar.mulShift_apply]
    have hcod : ∀ (ρ0 : Representation k (L' ≃ₐ[RatFunc Fq] L') V) (u : ℕ),
        Swan.cod (ρ0.comp (Slope1Sol.II Qh).subtype) ((Slope1Sol.RR Qh).lower u) =
          Module.finrank k V - Module.finrank k (Representation.invariants (ρ0.comp (G u).subtype)) := by
      intro ρ0 u
      have : Swan.fixd (ρ0.comp (Slope1Sol.II Qh).subtype) ((Slope1Sol.RR Qh).lower u) =
          Representation.invariants (ρ0.comp (G u).subtype) := by
        ext w
        rw [Swan.mem_fixd, Representation.mem_invariants]
        constructor
        · rintro hw ⟨σ, hσ⟩
          exact hw ⟨σ, Slope1Sol.G_le_inertia Qh G hG' u hσ⟩ ((Slope1Sol.mem_lower_iff' Qh G hG' u _).2 hσ)
        · intro hw τ hτ
          exact hw ⟨τ, (Slope1Sol.mem_lower_iff' Qh G hG' u τ).1 hτ⟩
      rw [Swan.cod, this]
    have hsw : ∑ᶠ u : ℕ, (Nat.card (G (u + 1)) : ℚ) / Nat.card (G 0) *
          ((Module.finrank k V - Module.finrank k
            (Representation.invariants (ρ'.comp (G (u + 1)).subtype)) : ℕ) : ℚ) =
        (Slope1Sol.RR Qh).swan (ρ'.comp (Slope1Sol.II Qh).subtype) := by
      rw [Swan.RamFn.swan, finsum_eq_sum_of_support_subset _ (s := Finset.range (Slope1Sol.RR Qh).top)]
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [Slope1Sol.card_lower Qh G hG', Slope1Sol.card_inertia Qh G hG', hcod]
      · intro u hu
        rw [Function.mem_support] at hu
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hu
        rw [← hcod, (Slope1Sol.RR Qh).lower_eq_bot (not_lt.1 hlt), Swan.cod_bot]
        simp
    rw [hsw, hρ'eq]
    exact hb
