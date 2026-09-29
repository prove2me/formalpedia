-- Prove2me | solution 1 for Subalgebra.mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2b65216c-3a69-5466-9a8a-572224786860

import Mathlib
import Theorems.Thm_Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin

set_option autoImplicit false

namespace FibreDimAux

open MvPolynomial

section valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

lemma exists_dvd_all (s : Finset R) : s = ∅ ∨ ∃ a ∈ s, ∀ b ∈ s, a ∣ b := by
  classical
  refine Finset.induction_on s (Or.inl rfl) ?_
  intro a s ha ih
  right
  rcases ih with rfl | ⟨b, hb, hball⟩
  · exact ⟨a, Finset.mem_insert_self a ∅, fun c hc => by
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact dvd_rfl
      · exact absurd hc (Finset.notMem_empty c)⟩
  · rcases ValuationRing.dvd_total a b with hab | hba
    · refine ⟨a, Finset.mem_insert_self a s, fun c hc => ?_⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact dvd_rfl
      · exact hab.trans (hball c hc)
    · refine ⟨b, Finset.mem_insert_of_mem hb, fun c hc => ?_⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hba
      · exact hball c hc

lemma exists_eq_C_mul_and_coeff_eq_one {σ : Type*} (F : MvPolynomial σ R) (hF : F ≠ 0) :
    ∃ (c : R) (F₀ : MvPolynomial σ R), c ≠ 0 ∧ F = C c * F₀ ∧ ∃ m, F₀.coeff m = 1 := by
  classical
  rcases exists_dvd_all (F.support.image fun m => F.coeff m) with h | ⟨c, hc, hall⟩
  · exfalso
    apply hF
    rw [Finset.image_eq_empty, support_eq_empty] at h
    exact h
  · obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hc
    have hc0 : F.coeff m₀ ≠ 0 := mem_support_iff.mp hm₀
    have hdvd : C (F.coeff m₀) ∣ F := by
      rw [C_dvd_iff_dvd_coeff]
      intro m
      by_cases hm : m ∈ F.support
      · exact hall _ (Finset.mem_image_of_mem _ hm)
      · rw [notMem_support_iff.mp hm]
        exact dvd_zero _
    obtain ⟨F₀, hF₀⟩ := hdvd
    refine ⟨F.coeff m₀, F₀, hc0, hF₀, m₀, ?_⟩
    have h1 : F.coeff m₀ = F.coeff m₀ * F₀.coeff m₀ := by
      conv_lhs => rw [hF₀]
      exact coeff_C_mul m₀ _ _
    exact (mul_eq_left₀ hc0).mp h1.symm

end valuation

section engine

variable {R B : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B]

theorem not_algebraicIndependent_quotient {ι : Type*}
    (hgen : ∀ w : ι → B, ¬ AlgebraicIndependent R w)
    (p : Ideal R) [p.IsMaximal] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p]
    (v : ι → B ⧸ Q) : ¬ AlgebraicIndependent (R ⧸ p) v := by
  classical
  intro hv

  have hw : ∃ w : ι → B, (fun i => Ideal.Quotient.mk Q (w i)) = v :=
    ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
      funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
  obtain ⟨w, rfl⟩ := hw

  have hdep := hgen w
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨F, hF0, hFne⟩ := hdep
  obtain ⟨c, F₀, hc, hF, m₀, hm₀⟩ := exists_eq_C_mul_and_coeff_eq_one F hFne
  have hF₀0 : aeval w F₀ = 0 := by
    rw [hF, map_mul, aeval_C] at hF0
    exact (mul_eq_zero.mp hF0).resolve_left
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R B)).mpr hc)

  have hnt : Nontrivial (R ⧸ p) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  set Fbar : MvPolynomial ι (R ⧸ p) := MvPolynomial.map (algebraMap R (R ⧸ p)) F₀ with hFbar
  have hFbar_ne : Fbar ≠ 0 := by
    intro h
    have h1 : Fbar.coeff m₀ = 1 := by
      rw [hFbar, coeff_map, hm₀, map_one]
    rw [h, coeff_zero] at h1
    exact zero_ne_one h1
  have hFbar0 : aeval (fun i => Ideal.Quotient.mk Q (w i)) Fbar = 0 := by
    rw [hFbar, aeval_map_algebraMap]
    have h2 := comp_aeval_apply (Ideal.Quotient.mkₐ R Q) (f := w) F₀
    simp only [Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [← h2, hF₀0, map_zero]
  exact hFbar_ne (hv.eq_zero_of_aeval_eq_zero Fbar hFbar0)

theorem forall_fin_not_algebraicIndependent_of_trdeg_le (d : ℕ)
    (htr : Algebra.trdeg R B ≤ d) (w : Fin (d + 1) → B) : ¬ AlgebraicIndependent R w := by
  intro hw
  have h := hw.lift_cardinalMk_le_trdeg
  rw [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] at h
  have h2 : ((d + 1 : ℕ) : Cardinal) ≤ (d : Cardinal) := h.trans htr
  norm_cast at h2
  omega

end engine

end FibreDimAux

namespace FibreDimAux

open MvPolynomial

section trdeg

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem trdeg_le_of_forall_fin (n : ℕ)
    (H : ∀ w : Fin (n + 1) → A, ¬ AlgebraicIndependent R w) :
    Algebra.trdeg R A ≤ n := by
  classical
  have key : ∀ s : Finset A, (AlgebraicIndependent R fun i : s => (i : A)) → s.card ≤ n := by
    intro s hs
    by_contra hlt
    have hle : n + 1 ≤ s.card := by omega

    let f : Fin (n + 1) → (s : Set A) := fun i => s.equivFin.symm (Fin.castLE hle i)
    have hf : Function.Injective f := by
      intro i j hij
      have := s.equivFin.symm.injective hij
      exact Fin.castLE_injective hle this
    exact H _ (hs.comp f hf)
  have bdd := algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded key
  unfold Algebra.trdeg
  apply ciSup_le'
  rintro ⟨s, hs⟩
  exact bdd s hs

end trdeg

section corollaries

variable {R B : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B]

theorem trdeg_quotient_le (d : ℕ) (htr : Algebra.trdeg R B ≤ d)
    (p : Ideal R) [p.IsMaximal] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    Algebra.trdeg (R ⧸ p) (B ⧸ Q) ≤ d :=
  trdeg_le_of_forall_fin d fun v =>
    not_algebraicIndependent_quotient
      (forall_fin_not_algebraicIndependent_of_trdeg_le d htr) p Q v

theorem dimensionLEOne_quotient [Algebra.FiniteType R B] (htr : Algebra.trdeg R B ≤ 1)
    (p : Ideal R) [p.IsMaximal] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    Ring.DimensionLEOne (B ⧸ Q) := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  haveI : Algebra.FiniteType (R ⧸ p) (B ⧸ Q) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ p) (B ⧸ Q)
  exact Ring.DimensionLEOne.of_finiteType_of_trdeg_le_one (R ⧸ p) (B ⧸ Q)
    (trdeg_quotient_le 1 htr p Q)

theorem isMaximal_of_lt [Algebra.FiniteType R B] (htr : Algebra.trdeg R B ≤ 1)
    (p : Ideal R) [p.IsMaximal] (Q Q' : Ideal B) [Q.IsPrime] [Q'.IsPrime] [Q.LiesOver p]
    (hQQ' : Q < Q') : Q'.IsMaximal := by
  have hdim := dimensionLEOne_quotient htr p Q

  have hprime : (Q'.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact hQQ'.le)
  have hne : Q'.map (Ideal.Quotient.mk Q) ≠ ⊥ := by
    intro h
    apply hQQ'.ne
    apply le_antisymm hQQ'.le
    intro x hx
    have : Ideal.Quotient.mk Q x ∈ Q'.map (Ideal.Quotient.mk Q) := Ideal.mem_map_of_mem _ hx
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hmax : (Q'.map (Ideal.Quotient.mk Q)).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hne hprime
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
    (K := Q'.map (Ideal.Quotient.mk Q))
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hQQ'.le] at this
  exact this

theorem mem_minimalPrimes_of_not_isMaximal [Algebra.FiniteType R B] (htr : Algebra.trdeg R B ≤ 1)
    (p : Ideal R) [p.IsMaximal] (ϖ : R) (hϖ : ϖ ∈ p) (hp : p = Ideal.span {ϖ})
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] (hQ : ¬ Q.IsMaximal) :
    Q ∈ (Ideal.span {algebraMap R B ϖ}).minimalPrimes := by
  have hϖQ : algebraMap R B ϖ ∈ Q := (Ideal.mem_of_liesOver Q p ϖ).mp hϖ
  have hle : Ideal.span {algebraMap R B ϖ} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hϖQ
  refine ⟨⟨inferInstance, hle⟩, ?_⟩
  rintro Q₀ ⟨hQ₀prime, hQ₀le⟩ hQ₀Q

  haveI := hQ₀prime
  have hQ₀over : Q₀.LiesOver p := by
    have h1 : p ≤ Q₀.under R := by
      rw [hp, Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      exact hQ₀le (Ideal.subset_span rfl)
    have h2 : Q₀.under R ≠ ⊤ := (inferInstance : (Q₀.under R).IsPrime).ne_top
    exact ⟨Ideal.IsMaximal.eq_of_le inferInstance h2 h1⟩
  by_contra hne
  have hlt : Q₀ < Q := lt_of_le_of_ne hQ₀Q (fun h => hne (h ▸ le_rfl))
  exact hQ (isMaximal_of_lt htr p Q₀ Q hlt)

end corollaries

end FibreDimAux

namespace FibreDimAux

lemma mem_adjoin_of_mem_adjoin_of_tower {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] (s : Set A)
    (x : A) (hx : x ∈ Algebra.adjoin R s) : x ∈ Algebra.adjoin S s := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap a =>
    rw [IsScalarTower.algebraMap_apply R S A a]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

lemma isAlgebraic_adjoin_of_tower {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] (s : Set A)
    (x : A) (hx : IsAlgebraic ↥(Algebra.adjoin R s) x) : IsAlgebraic ↥(Algebra.adjoin S s) x := by
  let f : ↥(Algebra.adjoin R s) →+* ↥(Algebra.adjoin S s) :=
    { toFun := fun y => ⟨y.1, mem_adjoin_of_mem_adjoin_of_tower s y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hfinj : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg Subtype.val h :)
  exact hx.ringHom_of_comp_eq f (RingHom.id A) hfinj (by ext; rfl)

lemma valuationRing_quotient_of_isMaximal {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal] :
    @ValuationRing (R ⧸ p) _ (Ideal.Quotient.isDomain p) := by
  have hkfield : IsField (R ⧸ p) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  refine ValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · exact Or.inl (by rw [ha, hb])
    · exact Or.inr (by rw [ha]; exact dvd_zero b)
  · obtain ⟨c, hc⟩ := hkfield.mul_inv_cancel ha
    exact Or.inl ⟨c * b, by rw [← mul_assoc, hc, one_mul]⟩

lemma bot_isMaximal_quotient_of_isMaximal {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal] :
    (⊥ : Ideal (R ⧸ p)).IsMaximal := by
  have hkfield : IsField (R ⧸ p) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  haveI := Ring.isField_iff_isSimpleOrder_ideal.mp hkfield
  exact ⟨isCoatom_bot⟩

theorem isMaximal_of_ne_bot_of_ker
    {A₀ : Type*} [CommRing A₀] {F : Type*} [Field F] [Algebra A₀ F]
    (B : Subalgebra A₀ F) [Algebra.FiniteType A₀ ↥B]
    (t : F) (halg : ∀ x : F, IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) x)
    (p : Ideal A₀) [p.IsMaximal] (hker : ∀ a ∈ p, algebraMap A₀ F a = 0)
    (𝔮 : Ideal ↥B) [𝔮.IsPrime] (hne : 𝔮 ≠ ⊥) : 𝔮.IsMaximal := by
  classical
  have hcoeB : ∀ a : A₀, ((algebraMap A₀ ↥B a : ↥B) : F) = algebraMap A₀ F a := fun a => rfl
  have hkerB : ∀ a ∈ p, algebraMap A₀ ↥B a = 0 := fun a ha =>
    Subtype.ext (by rw [hcoeB]; exact hker a ha)
  haveI : ValuationRing (A₀ ⧸ p) := valuationRing_quotient_of_isMaximal p
  haveI : (⊥ : Ideal (A₀ ⧸ p)).IsMaximal := bot_isMaximal_quotient_of_isMaximal p
  letI algkF : Algebra (A₀ ⧸ p) F := (Ideal.Quotient.lift p (algebraMap A₀ F) hker).toAlgebra
  haveI : IsScalarTower A₀ (A₀ ⧸ p) F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  letI algkB : Algebra (A₀ ⧸ p) ↥B := (Ideal.Quotient.lift p (algebraMap A₀ ↥B) hkerB).toAlgebra
  haveI : IsScalarTower A₀ (A₀ ⧸ p) ↥B := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : IsScalarTower (A₀ ⧸ p) ↥B F :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rfl)
  haveI : Algebra.FiniteType (A₀ ⧸ p) ↥B := Algebra.FiniteType.of_restrictScalars_finiteType A₀ (A₀ ⧸ p) ↥B
  have hkerBeq : RingHom.ker (algebraMap A₀ ↥B) = p := by
    refine (Ideal.IsMaximal.eq_of_le inferInstance (RingHom.ker_ne_top _) ?_).symm
    intro a ha
    exact hkerB a ha
  have hinjk : Function.Injective (algebraMap (A₀ ⧸ p) ↥B) := by
    show Function.Injective (Ideal.Quotient.lift p (algebraMap A₀ ↥B) hkerB)
    exact RingHom.lift_injective_of_ker_le_ideal p hkerB hkerBeq.le
  haveI : FaithfulSMul (A₀ ⧸ p) ↥B := (faithfulSMul_iff_algebraMap_injective (A₀ ⧸ p) ↥B).mpr hinjk
  haveI : (⊥ : Ideal ↥B).LiesOver (⊥ : Ideal (A₀ ⧸ p)) :=
    ⟨by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinjk]⟩
  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin (A₀ ⧸ p) ({t} : Set F)) F :=
    ⟨fun x => isAlgebraic_adjoin_of_tower ({t} : Set F) x (halg x)⟩
  have htrF : Algebra.trdeg (A₀ ⧸ p) F ≤ 1 := by
    simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk (A₀ ⧸ p) ({t} : Set F)
  have htrB : Algebra.trdeg (A₀ ⧸ p) ↥B ≤ 1 :=
    (trdeg_le_of_injective (IsScalarTower.toAlgHom (A₀ ⧸ p) ↥B F) Subtype.val_injective).trans htrF
  have hlt : (⊥ : Ideal ↥B) < 𝔮 := lt_of_le_of_ne bot_le (Ne.symm hne)
  exact isMaximal_of_lt htrB (⊥ : Ideal (A₀ ⧸ p)) ⊥ 𝔮 hlt

end FibreDimAux

open FibreDimAux in
theorem solution
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {F : Type} [Field F] [Algebra A₀ F]
    (B : Subalgebra A₀ F) (hBfg : B.FG)

    (t : F) (halg : ∀ x : F, IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) x)
    (𝔮 : Ideal ↥B) (h𝔮 : 𝔮.IsPrime)
    (hle : Ideal.map (algebraMap A₀ ↥B) (IsLocalRing.maximalIdeal A₀) ≤ 𝔮) (hmax : ¬ 𝔮.IsMaximal) :
    𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (IsLocalRing.maximalIdeal A₀)).minimalPrimes := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A₀
  have hm : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI := h𝔮
  haveI : Algebra.FiniteType A₀ ↥B := (Subalgebra.fg_iff_finiteType B).mp hBfg

  have hunder : IsLocalRing.maximalIdeal A₀ ≤ 𝔮.under A₀ := by
    rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap]; exact hle
  haveI hover : 𝔮.LiesOver (IsLocalRing.maximalIdeal A₀) :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance (inferInstance : (𝔮.under A₀).IsPrime).ne_top hunder⟩
  have hcoeB : ∀ a : A₀, ((algebraMap A₀ ↥B a : ↥B) : F) = algebraMap A₀ F a := fun a => rfl
  by_cases hinj : Function.Injective (algebraMap A₀ F)
  ·
    haveI : FaithfulSMul A₀ ↥B := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      apply hinj
      rw [← hcoeB, ← hcoeB, hab]
    haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F)) F := ⟨halg⟩
    have htrF : Algebra.trdeg A₀ F ≤ 1 := by
      simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk A₀ ({t} : Set F)
    have htrB : Algebra.trdeg A₀ ↥B ≤ 1 :=
      (trdeg_le_of_injective B.val Subtype.val_injective).trans htrF
    have key := mem_minimalPrimes_of_not_isMaximal htrB (IsLocalRing.maximalIdeal A₀) ϖ
      (hm ▸ Ideal.mem_span_singleton_self ϖ) hm 𝔮 hmax
    rwa [hm, Ideal.map_span, Set.image_singleton]
  ·
    have hker : ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ F a = 0 := by
      have hprime : (RingHom.ker (algebraMap A₀ F)).IsPrime := RingHom.ker_isPrime _
      have hne : RingHom.ker (algebraMap A₀ F) ≠ ⊥ := fun h =>
        hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
      have hmax' : (RingHom.ker (algebraMap A₀ F)).IsMaximal := hprime.isMaximal hne
      have heq := IsLocalRing.eq_maximalIdeal hmax'
      intro a ha
      rw [← heq] at ha
      exact ha
    have hkerB : ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ ↥B a = 0 := fun a ha =>
      Subtype.ext (by rw [hcoeB]; exact hker a ha)
    have hmapbot : Ideal.map (algebraMap A₀ ↥B) (IsLocalRing.maximalIdeal A₀) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      intro a ha
      exact hkerB a ha
    rw [hmapbot, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
    by_contra hne
    apply hmax
    exact FibreDimAux.isMaximal_of_ne_bot_of_ker B t halg (IsLocalRing.maximalIdeal A₀) hker 𝔮 hne

end S_Subalgebra_mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin
end P2MW
export P2MW.S_Subalgebra_mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin (solution)
