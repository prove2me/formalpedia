-- Prove2me | solution 1 for WeierstrassCurve.hasseInvariant_jFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d6218dcc-3e96-524b-a2e9-02dec2b9487d

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_WeierstrassCurve_natDegree_hasseInvariant_jFamily
import Theorems.Thm_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
import Theorems.Thm_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
import Theorems.Thm_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one
import Theorems.Thm_ModularCurve_card_eq_of_ssJSet
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_ModularCurve_zero_mem_ssJSetHasse_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSetHasse_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_hasseInvariant_jFamily
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_hasseInvariant_jFamily.WeierstrassCurve ModularCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "hasseInvariant natDegree_hasseInvariant_jFamily eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero rootMultiplicity_hasseInvariant_jFamily_eq_one"
namespace DKasm
p2m_open "WeierstrassCurve"

theorem eq_of_mul_eq {k : Type*} [Field k] {M H T : Polynomial k} {c d : k}
    (hH : H = C c * M) (hT : T = C d * M) (hM : M.coeff 0 ≠ 0) (h0 : H.coeff 0 = T.coeff 0) : H = T := by
  have : c = d := by
    rw [hH, hT, coeff_C_mul, coeff_C_mul] at h0
    exact mul_right_cancel₀ hM h0
  rw [hH, hT, this]

theorem main
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k)) =
      (1 + 1728 * Polynomial.X) ^ (2 * m + e₄ + e₆) *
        ∏ a ∈ S₀ \ {0, 1728}, (1 + Polynomial.C (1728 - a) * Polynomial.X) := by
  have hp : q.Prime := Fact.out
  set H := WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k)) with hHdef
  set S₁ := S₀ \ {0, 1728} with hS₁
  set r := 2 * m + e₄ + e₆ with hr

  have hcast : ∀ a : ℕ, (a : k) = 0 ↔ q ∣ a := fun a => CharP.cast_eq_zero_iff k q a
  have hsmall : ∀ a : ℕ, 0 < a → a < q → (a : k) ≠ 0 := fun a ha haq h =>
    absurd (Nat.le_of_dvd ha ((hcast a).mp h)) (not_le.mpr haq)
  have h2 : (2 : k) ≠ 0 := by exact_mod_cast hsmall 2 (by norm_num) (by omega)
  have h3 : (3 : k) ≠ 0 := by exact_mod_cast hsmall 3 (by norm_num) (by omega)
  have h1728 : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

  have hq2 : q % 2 = 1 := by
    rcases Nat.even_or_odd q with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (even_iff_two_dvd.mp h)) (by omega)
    · exact Nat.odd_iff.mp h
  have hq3 : q % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h); omega
  have hS₀H : ∀ a, a ∈ S₀ ↔ a ∈ ssJSetHasse q k := by
    intro a; rw [hS₀, ssJSet_eq_ssJSetHasse q (by omega) k]
  have hcard₀ := card_eq_of_ssJSet q hq k S₀ hS₀
  have h0mem : (0 : k) ∈ S₀ ↔ q % 3 = 2 := (hS₀H 0).trans (zero_mem_ssJSetHasse_iff q hq k)
  have h1728mem : (1728 : k) ∈ S₀ ↔ q % 4 = 3 := (hS₀H 1728).trans (ofNat1728_mem_ssJSetHasse_iff q hq k)
  have hcard₁ : S₁.card = m := by
    have hc : S₀.card = S₁.card + (S₀ ∩ {0, 1728}).card := by
      rw [hS₁, ← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter S₀ {0, 1728}), Finset.sdiff_union_inter]
    set ε₀ : ℕ := if (0 : k) ∈ S₀ then 1 else 0 with hε₀
    set ε₁ : ℕ := if (1728 : k) ∈ S₀ then 1 else 0 with hε₁
    have hI : (S₀ ∩ {0, 1728}).card = ε₀ + ε₁ := by
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.filter_insert, Finset.filter_singleton, hε₀, hε₁]
      by_cases h0 : (0 : k) ∈ S₀ <;> by_cases h1 : (1728 : k) ∈ S₀ <;>
        simp [h0, h1, h1728.symm]
    have hε₀' : ε₀ = if q % 3 = 2 then 1 else 0 := by
      by_cases h0 : (0 : k) ∈ S₀
      · rw [hε₀, if_pos h0, if_pos (h0mem.mp h0)]
      · rw [hε₀, if_neg h0, if_neg (fun h => h0 (h0mem.mpr h))]
    have hε₁' : ε₁ = if q % 4 = 3 then 1 else 0 := by
      by_cases h1 : (1728 : k) ∈ S₀
      · rw [hε₁, if_pos h1, if_pos (h1728mem.mp h1)]
      · rw [hε₁, if_neg h1, if_neg (fun h => h1 (h1728mem.mpr h))]
    rw [hI, hcard₀, hε₀', hε₁'] at hc
    split_ifs at hc <;> omega

  have hdeg : H.natDegree = (q - 1) / 4 := (natDegree_hasseInvariant_jFamily q hq k).1
  have hH0 : H.coeff 0 = 1 := (natDegree_hasseInvariant_jFamily q hq k).2
  have hN : (q - 1) / 4 = 3 * m + e₄ + e₆ := by omega
  have hH_ne : H ≠ 0 := fun h => by rw [h, coeff_zero] at hH0; exact zero_ne_one hH0

  set tc : k := -(1728 : k)⁻¹ with htc
  have hS₁mem : ∀ a ∈ S₁, a ∈ ssJSet q k ∧ a ≠ 0 ∧ a ≠ 1728 := by
    intro a ha
    rw [hS₁, Finset.mem_sdiff, hS₀] at ha
    exact ⟨ha.1, by simpa using ha.2⟩
  have hroot : ∀ a ∈ S₁, H.IsRoot (a - 1728)⁻¹ := fun a ha =>
    eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet q hq k a (hS₁mem a ha).1 (hS₁mem a ha).2.2
  have hmult : ∀ a ∈ S₁, H.rootMultiplicity (a - 1728)⁻¹ = 1 := fun a ha =>
    rootMultiplicity_hasseInvariant_jFamily_eq_one q hq k a (hS₁mem a ha).1 (hS₁mem a ha).2.1 (hS₁mem a ha).2.2

  set P : Polynomial k := ∏ a ∈ S₁, (X - C (a - 1728)⁻¹) with hP
  have hPdvd : P ∣ H := by
    refine Finset.prod_dvd_of_coprime ?_ (fun a ha => dvd_iff_isRoot.mpr (hroot a ha))
    intro a ha b hb hab
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    refine isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun h => hab ?_)
    have := inv_injective h
    exact sub_left_injective this
  obtain ⟨G, hHG⟩ := hPdvd
  have hPmonic : P.Monic := Polynomial.monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _
  have hPdeg : P.natDegree = m := by
    rw [hP, Polynomial.natDegree_prod _ _ fun a _ => X_sub_C_ne_zero _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    exact hcard₁
  have hG_ne : G ≠ 0 := by rintro rfl; rw [mul_zero] at hHG; exact hH_ne hHG
  have hGdeg : G.natDegree = r := by
    have h := congrArg Polynomial.natDegree hHG
    rw [Polynomial.natDegree_mul hPmonic.ne_zero hG_ne, hPdeg, hdeg, hN] at h
    omega

  have hGroot : ∀ t, G.IsRoot t → t = tc := by
    intro t ht
    by_contra hne
    have hc : 1 + 1728 * t ≠ 0 := by
      intro h; apply hne
      rw [htc]
      have : t * 1728 = -1 := by linear_combination h
      field_simp
      linear_combination this
    have hHt : H.eval t = 0 := by rw [hHG, eval_mul, show G.eval t = 0 from ht, mul_zero]
    obtain ⟨ht0, hmem⟩ := mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero q hq k t hHt hc
    set a' : k := 1728 + t⁻¹ with ha'
    have ha'1728 : a' ≠ 1728 := by rw [ha']; intro h; exact inv_ne_zero ht0 (by linear_combination h)
    have ha'0 : a' ≠ 0 := by
      intro h; apply hne; rw [htc]
      have : t⁻¹ = -1728 := by linear_combination h
      rw [← inv_inv t, this, inv_neg]
    have ha'S₁ : a' ∈ S₁ := by
      rw [hS₁, Finset.mem_sdiff, hS₀]; exact ⟨hmem, by simp [ha'0, ha'1728]⟩
    have hta' : (a' - 1728)⁻¹ = t := by rw [ha', add_sub_cancel_left, inv_inv]
    have h2 : (X - C t) ^ 2 ∣ H := by
      rw [hHG, sq]
      refine mul_dvd_mul ?_ (dvd_iff_isRoot.mpr ht)
      rw [← hta']; exact Finset.dvd_prod_of_mem _ ha'S₁
    have hle := (Polynomial.le_rootMultiplicity_iff hH_ne).mpr h2
    rw [← hta', hmult a' ha'S₁] at hle
    omega

  set lc : k := G.leadingCoeff with hlc
  have hGsplit : G = C lc * (X - C tc) ^ r := by
    have hcardr : G.roots.card = G.natDegree := IsAlgClosed.card_roots_eq_natDegree
    have hroots : G.roots = Multiset.replicate r tc := by
      refine Multiset.eq_replicate.mpr ⟨by rw [hcardr, hGdeg], fun t ht => hGroot t ((mem_roots hG_ne).mp ht)⟩
    have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcardr
    rw [hroots, Multiset.map_replicate, Multiset.prod_replicate, ← hlc] at h
    exact h.symm

  set M : Polynomial k := (X - C tc) ^ r * P with hM
  have hHM : H = C lc * M := by rw [hHG, hGsplit, hM]; ring
  have hf1 : (1 : Polynomial k) + 1728 * X = C (1728 : k) * (X - C tc) := by
    rw [htc, map_neg, sub_neg_eq_add, mul_add, ← map_mul, mul_inv_cancel₀ h1728, map_one, map_ofNat]; ring
  have hf2 : ∀ a ∈ S₁, (1 : Polynomial k) + C (1728 - a) * X = C (1728 - a) * (X - C (a - 1728)⁻¹) := by
    intro a ha
    have hne : a - 1728 ≠ 0 := sub_ne_zero.mpr (hS₁mem a ha).2.2
    rw [mul_sub, ← map_mul, show (1728 - a) * (a - 1728)⁻¹ = -1 by field_simp; ring, map_neg, map_one]; ring
  have hTfac : (1 + 1728 * Polynomial.X) ^ r * ∏ a ∈ S₁, (1 + Polynomial.C (1728 - a) * Polynomial.X)
      = C ((1728 : k) ^ r * ∏ a ∈ S₁, (1728 - a)) * M := by
    rw [hf1, Finset.prod_congr rfl hf2, Finset.prod_mul_distrib, mul_pow, ← map_pow, map_mul, map_prod, hM, hP]
    ring
  have hM0 : M.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, hM, hP, eval_mul, eval_pow, eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ?_)) (Finset.prod_ne_zero_iff.mpr fun a ha => neg_ne_zero.mpr ?_)
    · rw [htc]; exact neg_ne_zero.mpr (inv_ne_zero h1728)
    · exact inv_ne_zero (sub_ne_zero.mpr (hS₁mem a ha).2.2)
  have hT0 : ((1 + 1728 * Polynomial.X) ^ r * ∏ a ∈ S₁, (1 + Polynomial.C (1728 - a) * Polynomial.X)).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_prod]
    simp
  exact eq_of_mul_eq hHM hTfac hM0 (hH0.trans hT0.symm)

end WeierstrassCurve.DKasm

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ModularCurve.ssJSet q k) :
    WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k)) =
      (1 + 1728 * Polynomial.X) ^ (2 * m + e₄ + e₆) *
        ∏ a ∈ S₀ \ {0, 1728}, (1 + Polynomial.C (1728 - a) * Polynomial.X) :=
  WeierstrassCurve.DKasm.main q hq m e₄ e₆ hm he₄ he₆ k S₀ hS₀

end S_WeierstrassCurve_hasseInvariant_jFamily
end P2MW
export P2MW.S_WeierstrassCurve_hasseInvariant_jFamily (solution)
