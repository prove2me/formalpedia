-- Prove2me | solution 1 for ValuationSubring.exists_sub_mem_nonunits_of_finrank_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d19844dd-6290-5601-b7b2-d2f75805c403

import Mathlib
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card

set_option autoImplicit false

open Polynomial

namespace ValuationSubring
p2m_export "ValuationSubring" "comap mem_comap neg_mem mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff one_mem mem_or_inv_mem valuation_le_one_iff valuation exists_forall_mem_and_sub_mem_nonunits"
namespace CompleteSplitting
p2m_open "ValuationSubring"

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

theorem mul_lt_one_aux {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  calc a * b ≤ 1 * b := mul_le_mul' ha le_rfl
    _ = b := one_mul b
    _ < 1 := hb

section Over

variable {O : ValuationSubring F} {V : ValuationSubring F'}
  (hV : V.comap (algebraMap F F') = O)
include hV

theorem mem_iff (x : F) : algebraMap F F' x ∈ V ↔ x ∈ O := by
  rw [← ValuationSubring.mem_comap (A := V) (f := algebraMap F F'), hV]

theorem algebraMap_mem (x : O) : algebraMap F F' (x : F) ∈ V := (mem_iff hV _).mpr x.2

theorem lt_one_iff (x : F) : V.valuation (algebraMap F F' x) < 1 ↔ O.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero,
    ← map_inv₀, mem_iff hV]

theorem le_one (x : O) : V.valuation (algebraMap F F' (x : F)) ≤ 1 :=
  (V.valuation_le_one_iff _).mpr (algebraMap_mem hV x)

theorem eq_one_iff (x : F) : V.valuation (algebraMap F F' x) = 1 ↔ O.valuation x = 1 := by
  constructor
  · intro h
    have hle : O.valuation x ≤ 1 :=
      (O.valuation_le_one_iff x).mpr ((mem_iff hV x).mp ((V.valuation_le_one_iff _).mp h.le))
    have hnlt : ¬ O.valuation x < 1 := fun hlt => (ne_of_lt ((lt_one_iff hV x).mpr hlt)) h
    exact le_antisymm hle (not_lt.mp hnlt)
  · intro h
    have hle : V.valuation (algebraMap F F' x) ≤ 1 :=
      (V.valuation_le_one_iff _).mpr ((mem_iff hV x).mpr ((O.valuation_le_one_iff x).mp h.le))
    have hnlt : ¬ V.valuation (algebraMap F F' x) < 1 := fun hlt =>
      (ne_of_lt ((lt_one_iff hV x).mp hlt)) h
    exact le_antisymm hle (not_lt.mp hnlt)

end Over

section Incomparable

variable {O : ValuationSubring F} {V W : ValuationSubring F'}

theorem valuation_eq_one_of_le (hVW : V ≤ W) {u : F'} (hu : V.valuation u = 1) :
    W.valuation u = 1 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact zero_ne_one hu
  have h1 : W.valuation u ≤ 1 :=
    (W.valuation_le_one_iff u).mpr (hVW ((V.valuation_le_one_iff u).mp hu.le))
  have h2 : W.valuation u⁻¹ ≤ 1 :=
    (W.valuation_le_one_iff u⁻¹).mpr (hVW ((V.valuation_le_one_iff u⁻¹).mp
      (by rw [map_inv₀, hu, inv_one])))
  rw [map_inv₀] at h2
  have hne : W.valuation u ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hne)).mp h2)

theorem sum_ne_zero (hV : V.comap (algebraMap F F') = O) (hW : W.comap (algebraMap F F') = O)
    (hVW : V ≤ W) {y : F'} (hyV : V.valuation y < 1) (hyW : W.valuation y = 1)
    (c : ℕ → F) (hc : ∀ k, c k ∈ O) {j N : ℕ} (hjN : j < N) (hj : O.valuation (c j) = 1)
    (hlow : ∀ k < j, O.valuation (c k) < 1) :
    ∑ k ∈ Finset.range N, algebraMap F F' (c k) * y ^ k ≠ 0 := by
  intro hsum
  set t : ℕ → F' := fun k => algebraMap F F' (c k) * y ^ k with ht

  set H : F' := ∑ k ∈ Finset.Ico j N, algebraMap F F' (c k) * y ^ (k - j) with hH
  have hhigh : ∑ k ∈ Finset.Ico j N, t k = y ^ j * H := by
    rw [hH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hjk : j ≤ k := (Finset.mem_Ico.mp hk).1
    have hyk : y ^ k = y ^ j * y ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    simp only [ht, hyk]
    ring

  have hHV : V.valuation H = 1 := by
    rw [hH, Finset.sum_eq_sum_Ico_succ_bot hjN, Nat.sub_self, pow_zero, mul_one]
    have hrest : V.valuation
        (∑ k ∈ Finset.Ico (j + 1) N, algebraMap F F' (c k) * y ^ (k - j)) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
      have hjk : j + 1 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [map_mul, map_pow]
      refine mul_lt_one_aux (le_one hV ⟨c k, hc k⟩) ?_
      exact pow_lt_one₀ zero_le' hyV (by omega)
    have hcj : V.valuation (algebraMap F F' (c j)) = 1 := (eq_one_iff hV _).mpr hj
    rw [Valuation.map_add_eq_of_lt_left V.valuation (lt_of_lt_of_eq hrest hcj.symm), hcj]

  have hHW : W.valuation (y ^ j * H) = 1 := by
    rw [map_mul, map_pow, hyW, one_pow, one_mul]
    exact valuation_eq_one_of_le hVW hHV

  have hlowW : W.valuation (∑ k ∈ Finset.range j, t k) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
    have hkj : k < j := Finset.mem_range.mp hk
    simp only [ht]
    rw [map_mul, map_pow, hyW, one_pow, mul_one]
    exact (lt_one_iff hW _).mpr (hlow k hkj)

  have hsplit : ∑ k ∈ Finset.range N, t k =
      ∑ k ∈ Finset.range j, t k + ∑ k ∈ Finset.Ico j N, t k :=
    (Finset.sum_range_add_sum_Ico t hjN.le).symm
  have hsum' : ∑ k ∈ Finset.range N, t k = 0 := hsum
  rw [hsplit, hhigh] at hsum'
  have heq : y ^ j * H = -∑ k ∈ Finset.range j, t k := by linear_combination hsum'
  rw [heq, Valuation.map_neg] at hHW
  rw [hHW] at hlowW
  exact lt_irrefl 1 hlowW

theorem eq_of_le [Algebra.IsAlgebraic F F'] (hV : V.comap (algebraMap F F') = O)
    (hW : W.comap (algebraMap F F') = O) (hVW : V ≤ W) : V = W := by
  classical
  refine le_antisymm hVW fun x hxW => ?_
  by_contra hxV
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxV (zero_mem V)
  set y : F' := x⁻¹ with hy
  have hyV : y ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  have hyV1 : V.valuation y < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
    right
    rw [hy, inv_inv]
    exact hxV
  have hyW1 : W.valuation y = 1 := by
    have h1 : W.valuation x ≤ 1 := (W.valuation_le_one_iff x).mpr hxW
    have h2 : W.valuation y ≤ 1 := (W.valuation_le_one_iff y).mpr (hVW hyV)
    rw [hy, map_inv₀] at h2 ⊢
    have hne : W.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    have h3 : 1 ≤ W.valuation x := (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h2
    rw [le_antisymm h1 h3, inv_one]

  obtain ⟨p, hp0, hpy⟩ := Algebra.IsAlgebraic.isAlgebraic (R := F) y
  obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image p.support
    (fun k => O.valuation (p.coeff k)) (Polynomial.support_nonempty.mpr hp0)
  have hc0 : p.coeff k0 ≠ 0 := Polynomial.mem_support_iff.mp hk0
  have hv0 : O.valuation (p.coeff k0) ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  set c : ℕ → F := fun k => (p.coeff k0)⁻¹ * p.coeff k with hc
  have hcO : ∀ k, c k ∈ O := by
    intro k
    rw [← O.valuation_le_one_iff]
    simp only [hc, map_mul, map_inv₀]
    by_cases hk : k ∈ p.support
    · calc (O.valuation (p.coeff k0))⁻¹ * O.valuation (p.coeff k)
          ≤ (O.valuation (p.coeff k0))⁻¹ * O.valuation (p.coeff k0) :=
            mul_le_mul' le_rfl (hmax k hk)
        _ = 1 := inv_mul_cancel₀ hv0
    · rw [Polynomial.notMem_support_iff.mp hk, map_zero, mul_zero]
      exact zero_le'
  have hck0 : O.valuation (c k0) = 1 := by
    simp only [hc, map_mul, map_inv₀]
    exact inv_mul_cancel₀ hv0
  have hex : ∃ k, O.valuation (c k) = 1 := ⟨k0, hck0⟩
  set j := Nat.find hex with hjdef
  have hj : O.valuation (c j) = 1 := Nat.find_spec hex
  have hlow : ∀ k < j, O.valuation (c k) < 1 := fun k hk =>
    lt_of_le_of_ne ((O.valuation_le_one_iff _).mpr (hcO k)) (Nat.find_min hex hk)
  have hcj0 : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj
    exact zero_ne_one hj
  have hpj : p.coeff j ≠ 0 := by
    intro h
    apply hcj0
    simp only [hc, h, mul_zero]
  have hjN : j < p.natDegree + 1 := Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hpj)
  have hrel : ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap F F' (c k) * y ^ k = 0 := by
    have h := hpy
    rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self _) y] at h
    have hfac : ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap F F' (c k) * y ^ k =
        algebraMap F F' (p.coeff k0)⁻¹ *
          ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • y ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hc, map_mul, Algebra.smul_def, mul_assoc]
    rw [hfac, h, mul_zero]
  exact sum_ne_zero hV hW hVW hyV1 hyW1 c hcO hjN hj hlow hrel

end Incomparable

end ValuationSubring.CompleteSplitting

open ValuationSubring.CompleteSplitting in
theorem solution
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (x : F') (hx : x ∈ O' i) :
    ∃ y ∈ O, x - algebraMap F F' y ∈ (O' i).nonunits := by
  classical
  by_contra! hno

  have hR : ∀ k l, O' k ≤ O' l → k = l := fun k l hkl => hinj (eq_of_le (hO' k) (hO' l) hkl)

  have hz : ∀ k : ι, ∃ z : F', ∀ l, z ∈ O' l ∧ z - (if l = k then 1 else 0) ∈ (O' l).nonunits :=
    fun k => ValuationSubring.exists_forall_mem_and_sub_mem_nonunits O' hR
      (fun l => if l = k then 1 else 0)
      (fun l => by
        show (if l = k then (1 : F') else 0) ∈ O' l
        split_ifs
        · exact one_mem _
        · exact zero_mem _)
  choose z hz using hz
  obtain ⟨w, hw⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits O' hR
    (fun l => if l = i then x else 0)
    (fun l => by
      show (if l = i then x else 0) ∈ O' l
      split_ifs with h
      · rw [h]; exact hx
      · exact zero_mem _)

  have hxv : (O' i).valuation x ≤ 1 := ((O' i).valuation_le_one_iff x).mpr hx
  have hli : LinearIndependent F (fun o : Option ι => o.elim w z) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra! hne
    obtain ⟨o1, ho1⟩ := hne
    obtain ⟨o0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun o => O.valuation (c o))
      Finset.univ_nonempty
    have hc0 : c o0 ≠ 0 := by
      intro h
      have h1 := hmax o1 (Finset.mem_univ o1)
      rw [h, map_zero] at h1
      exact ho1 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le'))
    have hv0 : O.valuation (c o0) ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0

    obtain ⟨d, hdO, hd0, hdsum⟩ : ∃ d : Option ι → F, (∀ o, d o ∈ O) ∧ d o0 = 1 ∧
        algebraMap F F' (d none) * w + ∑ k, algebraMap F F' (d (some k)) * z k = 0 := by
      refine ⟨fun o => (c o0)⁻¹ * c o, fun o => ?_, inv_mul_cancel₀ hc0, ?_⟩
      · rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
        calc (O.valuation (c o0))⁻¹ * O.valuation (c o)
            ≤ (O.valuation (c o0))⁻¹ * O.valuation (c o0) :=
              mul_le_mul' le_rfl (hmax o (Finset.mem_univ o))
          _ = 1 := inv_mul_cancel₀ hv0
      · have h1 : ∑ o, ((c o0)⁻¹ * c o) • (o.elim w z : F') = 0 := by
          calc ∑ o, ((c o0)⁻¹ * c o) • (o.elim w z : F')
              = ∑ o, (c o0)⁻¹ • (c o • (o.elim w z : F')) :=
                Finset.sum_congr rfl fun o _ => (smul_smul _ _ _).symm
            _ = (c o0)⁻¹ • ∑ o, c o • (o.elim w z : F') := Finset.smul_sum.symm
            _ = 0 := by rw [hc, smul_zero]
        rw [Fintype.sum_option] at h1
        simpa only [Option.elim_none, Option.elim_some, Algebra.smul_def] using h1

    have key : ∀ l : ι, (O' l).valuation
        (algebraMap F F' (d none) * (if l = i then x else 0) + algebraMap F F' (d (some l))) < 1 := by
      intro l
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun k => algebraMap F F' (d (some k)) * z k) (Finset.mem_univ l)
      rw [← hsplit] at hdsum
      have hrel : algebraMap F F' (d none) * (if l = i then x else 0) + algebraMap F F' (d (some l)) =
          algebraMap F F' (d none) * ((if l = i then x else 0) - w)
            - algebraMap F F' (d (some l)) * (z l - 1)
            - ∑ k ∈ Finset.univ.erase l, algebraMap F F' (d (some k)) * z k := by
        linear_combination hdsum
      rw [hrel]
      refine Valuation.map_sub_lt _ (Valuation.map_sub_lt _ ?_ ?_) ?_
      · rw [map_mul]
        refine mul_lt_one_aux (le_one (hO' l) ⟨_, hdO none⟩) ?_
        rw [Valuation.map_sub_swap]
        exact (hw l).2
      · rw [map_mul]
        refine mul_lt_one_aux (le_one (hO' l) ⟨_, hdO (some l)⟩) ?_
        have h := (hz l l).2
        rwa [if_pos rfl] at h
      · refine Valuation.map_sum_lt _ one_ne_zero fun k hk => ?_
        have hkl : k ≠ l := Finset.ne_of_mem_erase hk
        rw [map_mul]
        refine mul_lt_one_aux (le_one (hO' l) ⟨_, hdO (some k)⟩) ?_
        have h := (hz k l).2
        rwa [if_neg (fun h' => hkl h'.symm), sub_zero] at h

    rcases o0 with _ | k0
    ·
      have hk := key i
      rw [if_pos rfl, hd0, map_one, one_mul] at hk
      refine hno (-(d (some i))) (neg_mem (hdO (some i))) ?_
      rw [map_neg, sub_neg_eq_add]
      exact hk
    · by_cases hk0 : k0 = i
      ·
        rw [hk0] at hd0
        have hk := key i
        rw [if_pos rfl, hd0, map_one] at hk
        by_cases hdn : O.valuation (d none) < 1
        · have h1 : (O' i).valuation (algebraMap F F' (d none) * x) < 1 := by
            rw [map_mul]
            calc (O' i).valuation (algebraMap F F' (d none)) * (O' i).valuation x
                ≤ (O' i).valuation (algebraMap F F' (d none)) * 1 := mul_le_mul' le_rfl hxv
              _ = (O' i).valuation (algebraMap F F' (d none)) := mul_one _
              _ < 1 := (lt_one_iff (hO' i) _).mpr hdn
          have h2 := Valuation.map_sub_lt _ hk h1
          rw [add_sub_cancel_left, map_one] at h2
          exact lt_irrefl 1 h2
        · have hdn1 : O.valuation (d none) = 1 :=
            le_antisymm ((O.valuation_le_one_iff _).mpr (hdO none)) (not_lt.mp hdn)
          have hdn0 : d none ≠ 0 := by
            intro h
            rw [h, map_zero] at hdn1
            exact zero_ne_one hdn1
          have hne : algebraMap F F' (d none) ≠ 0 := (_root_.map_ne_zero _).mpr hdn0
          have hyO : -(d none)⁻¹ ∈ O :=
            neg_mem ((O.valuation_le_one_iff _).mp (by rw [map_inv₀, hdn1, inv_one]))
          refine hno _ hyO ?_
          have hxe : x - algebraMap F F' (-(d none)⁻¹) =
              algebraMap F F' (d none)⁻¹ * (algebraMap F F' (d none) * x + 1) := by
            rw [map_neg, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, map_inv₀,
              inv_mul_cancel₀ hne, one_mul]
          show (O' i).valuation (x - algebraMap F F' (-(d none)⁻¹)) < 1
          have hv1 : (O' i).valuation (algebraMap F F' (d none)) = 1 :=
            (eq_one_iff (hO' i) _).mpr hdn1
          rw [hxe, map_mul, map_inv₀, map_inv₀, hv1, inv_one, one_mul]
          exact hk
      ·
        have hk := key k0
        rw [if_neg hk0, mul_zero, zero_add, hd0, map_one] at hk
        exact lt_irrefl 1 hk

  have hcard' := hli.fintype_card_le_finrank
  rw [Fintype.card_option] at hcard'
  omega

end S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card
end P2MW
export P2MW.S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card (solution)
