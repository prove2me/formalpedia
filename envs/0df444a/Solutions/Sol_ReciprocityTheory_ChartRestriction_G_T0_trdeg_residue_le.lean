-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.trdeg_residue_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:16.061151+00:00
-- url     : https://prove2.me/submissions/5daa762a-2aa4-49d3-8422-7180af00c038

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_valuationRing
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_residueTrdegLe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D : ℕ)
    (hD : Algebra.trdeg K Ω = D) (v : AddValuation Ω (WithTop ℤ))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0) (a0 : Ω) (ha0 : a0 ≠ 0) (hva0 : v a0 ≠ 0) :
    letI := resAlg (F := K) v
    Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (vRing v)) ≤ ((D - 1 : ℕ) : Cardinal) := by
  set V := vRing v with hV
  set k := IsLocalRing.ResidueField (V.comap (algebraMap K Ω)) with hk
  set κ := IsLocalRing.ResidueField V with hκ
  letI inst : Algebra k κ := resAlg (F := K) v
  have hKV : ∀ a : K, algebraMap K Ω a ∈ V := by
    intro a
    rw [hV, mem_valuationRing]
    by_cases ha : a = 0
    · rw [ha, map_zero, AddValuation.map_zero]
      exact le_top
    · exact le_of_eq (hK a ha).symm
  let jK : K →+* V := (algebraMap K Ω).codRestrict V hKV
  let jW : K →+* V.comap (algebraMap K Ω) :=
    (RingHom.id K).codRestrict (V.comap (algebraMap K Ω)) fun a => ValuationSubring.mem_comap.mpr (hKV a)
  let ιK : K →+* k := (IsLocalRing.residue _).comp jW
  have hcompat : ∀ a : K, algebraMap k κ (ιK a) = IsLocalRing.residue V (jK a) := by
    intro a
    show IsLocalRing.ResidueField.map (comapIncl V (algebraMap K Ω)) (IsLocalRing.residue _ (jW a)) = _
    rw [IsLocalRing.ResidueField.map_residue]
    rfl
  have hle : Algebra.trdeg k κ ≤ D := by
    have h := ReciprocityTheory.MultiplicativeHeights.residueTrdegLe K Ω V
    rw [hD] at h
    exact h
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Algebra.trdeg k κ = r :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hle (Cardinal.nat_lt_aleph0 D))
  haveI : FaithfulSMul k κ :=
    (faithfulSMul_iff_algebraMap_injective k κ).mpr (algebraMap k κ).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hsr : Cardinal.mk s = r := by rw [hs.cardinalMk_eq_trdeg, hr]
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hsr
  let ρ : Fin r → κ := fun i => (e.symm i : κ)
  have hρ : AlgebraicIndependent k ρ := hs.1.comp e.symm e.symm.injective
  choose tV htV using fun i => IsLocalRing.residue_surjective (R := V) (ρ i)
  let t : Fin r → Ω := fun i => (tV i : Ω)
  let ψ : MvPolynomial (Fin r) K →+* V := MvPolynomial.eval₂Hom jK tV
  have hψ : ∀ p, (ψ p : Ω) = MvPolynomial.aeval t p := by
    intro p
    show V.subtype (MvPolynomial.eval₂ jK tV p) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
  have hres : ∀ p, IsLocalRing.residue V (ψ p) = MvPolynomial.aeval ρ (p.map ιK) := by
    intro p
    show IsLocalRing.residue V (MvPolynomial.eval₂ jK tV p) = _
    have hf : (IsLocalRing.residue V).comp jK = (algebraMap k κ).comp ιK :=
      RingHom.ext fun a => (hcompat a).symm
    have hg : (fun i => IsLocalRing.residue V (tV i)) = ρ := funext htV
    rw [MvPolynomial.hom_eval₂, hf, hg, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hG : ∀ p : MvPolynomial (Fin r) K, p ≠ 0 → v (MvPolynomial.aeval t p) = 0 := by
    intro p hp
    have hne : MvPolynomial.aeval ρ (p.map ιK) ≠ 0 := by
      intro h0
      apply hp
      apply MvPolynomial.map_injective ιK ιK.injective
      rw [map_zero]
      exact (algebraicIndependent_iff.mp hρ) _ h0
    rw [← hres] at hne
    have hu := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
    rw [← hψ]
    obtain ⟨u, hu'⟩ := hu
    have hmul : (ψ p : Ω) * ((↑u⁻¹ : V) : Ω) = 1 := by
      have h1 := u.mul_inv
      rw [hu'] at h1
      exact congrArg Subtype.val h1
    have hsum : v (ψ p : Ω) + v ((↑u⁻¹ : V) : Ω) = 0 := by
      rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v _).mp (ψ p).2)
      ((mem_valuationRing v _).mp (↑u⁻¹ : V).2)).mp hsum).1
  have ht : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    have h1 := hG p hne
    rw [hp, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : WithTop ℤ) = v a0 :=
    WithTop.ne_top_iff_exists.mp (by rw [Ne, AddValuation.top_iff]; exact ha0)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hva0 hm.symm
  have htr : Transcendental (Algebra.adjoin K (Set.range t)) a0 := by
    rintro ⟨q, hq0, hq⟩
    have hcv : ∀ j, q.coeff j ≠ 0 → v ((q.coeff j : Ω)) = 0 := by
      intro j hj
      have hmem : (q.coeff j : Ω) ∈ (MvPolynomial.aeval (R := K) t).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval K t]
        exact (q.coeff j).2
      obtain ⟨p, hp⟩ := hmem
      have hp0 : p ≠ 0 := by
        rintro rfl
        apply hj
        apply Subtype.ext
        rw [← hp, map_zero]
        rfl
      rw [← hp]
      exact hG p hp0
    rw [Polynomial.aeval_eq_sum_range] at hq
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image q.support (fun j => (j : ℤ) * m)
      (Polynomial.nonempty_support_iff.mpr hq0)
    have hj0S : j0 ∈ Finset.range (q.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp j0 hj0))
    have hterm : ∀ j, q.coeff j ≠ 0 → v (q.coeff j • a0 ^ j) = (((j : ℤ) * m : ℤ) : WithTop ℤ) := by
      intro j hj
      rw [Algebra.smul_def, AddValuation.map_mul, AddValuation.map_pow, ← hm]
      have e1 : algebraMap (Algebra.adjoin K (Set.range t)) Ω (q.coeff j) = (q.coeff j : Ω) := rfl
      rw [e1, hcv j hj, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul]
    have hg : v (q.coeff j0 • a0 ^ j0) = (((j0 : ℤ) * m : ℤ) : WithTop ℤ) :=
      hterm j0 (Polynomial.mem_support_iff.mp hj0)
    have hrest : v (q.coeff j0 • a0 ^ j0) <
        v (∑ j ∈ (Finset.range (q.natDegree + 1)).erase j0, q.coeff j • a0 ^ j) := by
      rw [hg]
      apply AddValuation.map_lt_sum _ WithTop.coe_ne_top
      intro j hj
      by_cases hc : q.coeff j = 0
      · rw [hc, zero_smul, AddValuation.map_zero]
        exact WithTop.coe_lt_top _
      · rw [hterm j hc, WithTop.coe_lt_coe]
        have hne : j ≠ j0 := Finset.ne_of_mem_erase hj
        have hle := hmin j (Polynomial.mem_support_iff.mpr hc)
        have hneq : (j0 : ℤ) * m ≠ (j : ℤ) * m := by
          intro h
          apply hne
          exact_mod_cast (mul_right_cancel₀ hm0 h).symm
        exact lt_of_le_of_ne hle hneq
    rw [← Finset.add_sum_erase _ _ hj0S] at hq
    have h2 := AddValuation.map_add_eq_of_lt_left v hrest
    rw [hq, AddValuation.map_zero, hg] at h2
    exact WithTop.top_ne_coe h2
  have hind : AlgebraicIndependent K (fun o : Option (Fin r) => o.elim a0 t) :=
    AlgebraicIndependent.option_iff.mpr ⟨ht, htr⟩
  have hcardle := hind.cardinalMk_le_trdeg
  rw [hD, Cardinal.mk_option, Cardinal.mk_fintype, Fintype.card_fin] at hcardle
  have hrD : r + 1 ≤ D := by exact_mod_cast hcardle
  have hfin : Algebra.trdeg k κ ≤ ((D - 1 : ℕ) : Cardinal) := by
    rw [hr]
    exact_mod_cast (by omega : r ≤ D - 1)
  exact hfin
end ReciprocityTheory.ChartRestriction.G.T0
