-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.u3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:15.671494+00:00
-- url     : https://prove2.me/submissions/95bd02a1-4c76-41bf-be45-4dde81f8ff59

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsAlt
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
import Definitions.Def_ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_U3_pow_mem__9e39d2041606
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_exists_charEquiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_exists_primRoot
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_exists_teichChar
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_finZ_val
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_fourierMap_smul_lambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_span_eq_of_vdet_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_gamma
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_vdet_le_of_span_le
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_vdet_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.U3
private theorem stab_lemma {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (AA : HopfOrder (C := C) R (ZMod p)) (k : ℕ) :
    ∀ f ∈ AA.carrier, (fun a : ZMod p => f ((k : ZMod p) * a)) ∈ AA.carrier := by
  induction k with
  | zero =>
    intro f hf
    obtain ⟨r, hr⟩ := (AA.le_int hf : ∀ x, ∃ r : R, algebraMap R C r = f x) 0
    have e : (fun a : ZMod p => f (((0 : ℕ) : ZMod p) * a)) = r • (1 : ZMod p → C) := by
      funext a
      simp [Algebra.smul_def, hr]
    rw [e]
    exact AA.carrier.smul_mem r AA.one_mem
  | succ k ih =>
    intro f hf
    have hle : tensorSpan R AA.carrier ≤ AA.carrier.comap
        (LinearMap.funLeft R C (fun a : ZMod p => ((k : ZMod p) * a, a))) := by
      unfold tensorSpan
      refine Submodule.span_le.mpr ?_
      rintro F ⟨g, hg, h, hh, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have e : (LinearMap.funLeft R C (fun a : ZMod p => ((k : ZMod p) * a, a)))
          (fun q : ZMod p × ZMod p => g q.1 * h q.2) = (fun a => g ((k : ZMod p) * a)) * h := by
        funext a
        simp [LinearMap.funLeft_apply]
      rw [e]
      exact AA.mul_mem _ _ (ih g hg) hh
    have e : (fun a : ZMod p => f (((k + 1 : ℕ) : ZMod p) * a)) =
        (LinearMap.funLeft R C (fun a : ZMod p => ((k : ZMod p) * a, a))) (addPull R (ZMod p) f) := by
      funext a
      simp [addPull, LinearMap.funLeft_apply, add_mul]
    rw [e]
    exact hle (AA.comul f hf)
private theorem pow_two_mul_p_sub_three_mul_self_eq_one {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {ω : ZMod p → C}
    (hpow : ∀ a, ω a ^ p = ω a) (hone : ω 1 = 1) (hmul : ∀ a b, ω (a * b) = ω a * ω b)
    (a : ZMod p) (ha : a ≠ 0) : ω a ^ (2 * p - 3) * ω a = 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have hinv : ω a * ω a⁻¹ = 1 := by rw [← hmul, mul_inv_cancel₀ ha, hone]
  have hne : ω a ≠ 0 := left_ne_zero_of_mul_eq_one hinv
  have h1 : ω a ^ (p - 1) = 1 := by
    have h2 : ω a ^ (p - 1) * ω a = 1 * ω a := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hpow, one_mul]
    exact mul_right_cancel₀ hne h2
  have h3 : 2 * p - 3 + 1 = (p - 1) * 2 := by omega
  rw [← pow_succ, h3, pow_mul, h1, one_pow]
private theorem sum_wt_mul_comp_mul_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {ω : ZMod p → C}
    (hpow : ∀ a, ω a ^ p = ω a) (hone : ω 1 = 1) (hmul : ∀ a b, ω (a * b) = ω a * ω b)
    (a : ZMod p) (ha : a ≠ 0) (f : ZMod p → C) :
    ∑ k, wt ω k * f (k * a) = ω a * ∑ b, wt ω b * f b := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight₀ a ha) _ _ ?_
  intro k
  have h := pow_two_mul_p_sub_three_mul_self_eq_one hpow hone hmul a ha
  show wt ω k * f (k * a) = ω a * (wt ω (k * a) * f (k * a))
  simp only [wt, hmul, mul_pow]
  linear_combination (-(ω k ^ (2 * p - 3) * f (k * a))) * h
private theorem valuation_sub_one_eq_one_of_lt_one {C : Type} [Field C] (v : Valuation C NNReal) (q : C) (hq : v q < 1) :
    v (q - 1) = 1 := by
  apply le_antisymm
  · calc v (q - 1) ≤ max (v q) (v 1) := Valuation.map_sub v q 1
      _ ≤ 1 := by rw [v.map_one]; exact max_le hq.le le_rfl
  · by_contra h
    push_neg at h
    have h2 := Valuation.map_sub v q (q - 1)
    rw [sub_sub_cancel, v.map_one] at h2
    exact absurd h2 (not_le.mpr (max_lt hq h))
private theorem valuation_le_one_of_sub_natCast_lt_one {p : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
    [CommRing R] [Algebra R C] (hv : v.Integers R) (z : C) (k : ZMod p)
    (h : v (z - (k.val : C)) < 1) : v z ≤ 1 := by
  have hk : v (k.val : C) ≤ 1 := by
    have h2 := hv.map_le_one (k.val : R)
    simpa using h2
  calc v z = v ((z - (k.val : C)) + (k.val : C)) := by rw [sub_add_cancel]
    _ ≤ max (v (z - (k.val : C))) (v (k.val : C)) := Valuation.map_add v _ _
    _ ≤ 1 := max_le h.le hk
private theorem augIdeal_eq_span_pow_of_span_pow {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (M : Submodule R (ZMod p → C)) (x : ZMod p → C) (hx0 : x 0 = 0)
    (hM : M = Submodule.span R (Set.range fun j : Fin p => x ^ (j : ℕ))) :
    augIdeal M = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} := by
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  apply le_antisymm
  · intro f hf
    simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hf
    obtain ⟨hfM, hf0⟩ := hf
    rw [hM, Submodule.mem_span_range_iff_exists_fun] at hfM
    obtain ⟨cf, rfl⟩ := hfM
    have hc0 : algebraMap R C (cf ⟨0, hpos⟩) = 0 := by
      rw [Finset.sum_apply, Finset.sum_eq_single ⟨0, hpos⟩] at hf0
      · simpa [Algebra.smul_def] using hf0
      · intro j _ hj
        have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
        simp [hx0, zero_pow hj']
      · simp
    refine Submodule.sum_mem _ (fun j _ => ?_)
    by_cases hj : (j : ℕ) = 0
    · have hj0 : j = ⟨0, hpos⟩ := Fin.ext hj
      subst hj0
      have hz : cf ⟨0, hpos⟩ • x ^ ((⟨0, hpos⟩ : Fin p) : ℕ) = 0 := by
        funext a
        simp only [Pi.smul_apply, Pi.pow_apply, Fin.val_mk, pow_zero, Pi.zero_apply,
          Algebra.smul_def, hc0, zero_mul]
      rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨j, Nat.one_le_iff_ne_zero.mpr hj, j.isLt, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, hj1, hjp, rfl⟩
    simp only [SetLike.mem_coe, augIdeal, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.proj_apply]
    refine ⟨?_, ?_⟩
    · rw [hM]
      exact Submodule.subset_span ⟨⟨j, hjp⟩, rfl⟩
    · simp [hx0, zero_pow (by omega : j ≠ 0)]
private theorem sqIdeal_eq_span_of_pow_p_eq_smul {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (x : ZMod p → C) (δ : R) (hxp : x ^ p = fun a => algebraMap R C δ * x a)
    (I : Submodule R (ZMod p → C))
    (hI : I = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j}) :
    sqIdeal I = Submodule.span R
        ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) := by
  have hp2 := (Fact.out : p.Prime).two_le
  set T := Submodule.span R
    ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) with hT
  have hδ : (fun a => algebraMap R C δ * x a) = δ • x := by
    funext a
    simp [Algebra.smul_def]
  have hpow : ∀ n, 2 ≤ n → n ≤ 2 * p - 2 → x ^ n ∈ T := by
    intro n hn2 hn
    by_cases hnp : n < p
    · exact Submodule.subset_span (Or.inr ⟨n, hn2, hnp, rfl⟩)
    · push_neg at hnp
      obtain ⟨k, rfl⟩ : ∃ k, n = p + k := ⟨n - p, by omega⟩
      have hsplit : x ^ (p + k) = δ • x ^ (k + 1) := by
        rw [pow_add, hxp, hδ, smul_mul_assoc, ← pow_succ']
      rw [hsplit]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [zero_add, pow_one, ← hδ]
        exact Submodule.subset_span (Or.inl rfl)
      · exact T.smul_mem δ (Submodule.subset_span (Or.inr ⟨k + 1, by omega, by omega, rfl⟩))
  have hxI : ∀ j, 1 ≤ j → j < p → x ^ j ∈ I := fun j h1 h2 => by
    rw [hI]
    exact Submodule.subset_span ⟨j, h1, h2, rfl⟩
  apply le_antisymm
  · unfold sqIdeal
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    have key : ∀ i, 1 ≤ i → i < p → ∀ g ∈ I, x ^ i * g ∈ T := by
      intro i hi1 hip g hg
      rw [hI] at hg
      have hle : Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} ≤
          T.comap (LinearMap.mulLeft R (x ^ i)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨k, hk1, hkp, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, ← pow_add]
        exact hpow _ (by omega) (by omega)
      exact hle hg
    have hle2 : I ≤ T.comap (LinearMap.mulRight R f') := by
      rw [hI]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi1, hip, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
      exact key i hi1 hip f' hf'
    exact hle2 hf
  · refine Submodule.span_le.mpr ?_
    rintro y (rfl | ⟨j, hj2, hjp, rfl⟩)
    · rw [SetLike.mem_coe]
      unfold sqIdeal
      refine Submodule.subset_span ⟨x ^ 1, hxI 1 le_rfl (by omega), x ^ (p - 1),
        hxI (p - 1) (by omega) (by omega), ?_⟩
      rw [← hxp, ← pow_add]
      congr 1
      omega
    · rw [SetLike.mem_coe]
      unfold sqIdeal
      refine Submodule.subset_span ⟨x ^ 1, hxI 1 le_rfl (by omega), x ^ (j - 1),
        hxI (j - 1) (by omega) (by omega), ?_⟩
      rw [← pow_add]
      congr 1
      omega
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.U3
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : PrimeHopfOrderStatement := by
  intro p hpf C _ _ _ v R _ _ hv hpv AA
  have hprime : p.Prime := hpf.out
  haveI : NeZero p := ⟨hprime.ne_zero⟩
  obtain ⟨ω, hωpow, hωcong, hω0, hω1, hωmul, hωsep⟩ := exists_teichChar hv hpv
  have hT : IsTeich v ω := ⟨hωpow, hωcong, hω0, hω1, hωmul, hωsep⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : C, IsPrimitiveRoot ζ p := exists_primRoot
  obtain ⟨e, he1, he2⟩ := exists_charEquiv hζ
  obtain ⟨AD, hAD1, -, hcol⟩ := ReciprocityTheory.PGsh.L2.h1 C R v hv (ZMod p) (ZMod p) e he1 rfl AA
  obtain ⟨BA, hBAu, hBA⟩ := AA.lat
  obtain ⟨BD, hBDu, hBD⟩ := AD.lat
  have hcc := hcol (v BA.det) (v BD.det) ⟨BA, hBA, rfl⟩ ⟨BD, hBD, rfl⟩
  rw [ZMod.card] at hcc
  have hvp1 : v ((p : C) - 1) = 1 := valuation_sub_one_eq_one_of_lt_one v _ hpv
  have hq0 : (p : C) - 1 ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hvp1
    exact zero_ne_one hvp1
  have hsumω : ∑ a, u0 ω a * ω a = (p : C) - 1 := by
    have hterm : ∀ a, u0 ω a * ω a = 1 - if a = 0 then 1 else 0 := by
      intro a
      by_cases ha : a = 0
      · subst ha
        simp [hω0]
      · rw [if_neg ha, sub_zero]
        simp only [u0, if_neg ha, sub_zero]
        exact pow_two_mul_p_sub_three_mul_self_eq_one hωpow hω1 hωmul a ha
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    simp [Finset.sum_sub_distrib, Finset.card_univ, ZMod.card]
  obtain ⟨j0, -, hj0'⟩ := Finset.exists_max_image Finset.univ
    (fun j => v (∑ a, u0 ω a * BA a j)) Finset.univ_nonempty
  have hj0 : ∀ j, v (∑ a, u0 ω a * BA a j) ≤ v (∑ a, u0 ω a * BA a j0) :=
    fun j => hj0' j (Finset.mem_univ _)
  clear hj0'
  set m := ∑ a, u0 ω a * BA a j0 with hmdef
  have hm : m ≠ 0 := by
    intro hm0
    have hall : ∀ j, (∑ a, u0 ω a * BA a j) = 0 := by
      intro j
      have h := hj0 j
      rw [hm0, Valuation.map_zero] at h
      exact (Valuation.zero_iff v).mp (le_antisymm h (by positivity))
    have hinv : BA * BA⁻¹ = 1 := Matrix.mul_nonsing_inv BA hBAu
    obtain ⟨w, hw⟩ : ∃ w : ZMod p → C, ∀ a, ω a = ∑ j, BA a j * w j := by
      refine ⟨fun j => ∑ k, BA⁻¹ j k * ω k, fun a => ?_⟩
      have h1 : ∑ k, (BA * BA⁻¹) a k * ω k = ω a := by
        rw [hinv]
        simp [Matrix.one_apply]
      calc ω a = ∑ k, (BA * BA⁻¹) a k * ω k := h1.symm
        _ = ∑ j, BA a j * ∑ k, BA⁻¹ j k * ω k := by
          simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
    have h0 : ∑ a, u0 ω a * ω a = 0 := by
      calc ∑ a, u0 ω a * ω a = ∑ a, ∑ j, u0 ω a * BA a j * w j := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [hw a, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = ∑ j, ∑ a, u0 ω a * BA a j * w j := Finset.sum_comm
        _ = ∑ j, (∑ a, u0 ω a * BA a j) * w j := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_mul]
        _ = 0 := Finset.sum_eq_zero (fun j _ => by rw [hall j, zero_mul])
    rw [hsumω] at h0
    exact hq0 h0
  have hvm : v m ≠ 0 := (Valuation.ne_zero_iff v).mpr hm
  have hcolR : ∀ j, ∃ r : R, algebraMap R C r = (∑ a, u0 ω a * BA a j) * m⁻¹ := by
    intro j
    apply hv.exists_of_le_one
    rw [map_mul, map_inv₀]
    calc v (∑ a, u0 ω a * BA a j) * (v m)⁻¹ ≤ v m * (v m)⁻¹ :=
        mul_le_mul_of_nonneg_right (hj0 j) (by positivity)
      _ = 1 := mul_inv_cancel₀ hvm
  have hP : AA.carrier ≤ dualLat (Submodule.span R {fun a => m⁻¹ * u0 ω a}) := by
    rw [hBA]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    show ∀ g ∈ Submodule.span R {fun a => m⁻¹ * u0 ω a},
      ∃ r : R, algebraMap R C r = ∑ a, BA a j * g a
    intro g hg
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hg
    obtain ⟨r, hr⟩ := hcolR j
    refine ⟨s * r, ?_⟩
    rw [map_mul, hr, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Pi.smul_apply, Algebra.smul_def]
    ring
  have hu : (fun a => m⁻¹ * u0 ω a) ∈ dualLat AA.carrier := by
    show ∀ f ∈ AA.carrier, ∃ r : R, algebraMap R C r = ∑ a, m⁻¹ * u0 ω a * f a
    intro f hf
    have hf' : ∀ g ∈ Submodule.span R {fun a => m⁻¹ * u0 ω a},
        ∃ r : R, algebraMap R C r = ∑ a, f a * g a := hP hf
    obtain ⟨r', hr'⟩ := hf' _ (Submodule.mem_span_singleton_self _)
    exact ⟨r', by rw [hr']; exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)⟩
  have hyAD : fourier (R := R) (fun h a => e h a) (fun a => m⁻¹ * u0 ω a) ∈ AD.carrier := by
    rw [hAD1]
    exact Submodule.mem_map_of_mem hu
  rw [fourierMap_smul_lambdaWeight (R := R) hT e he2 m⁻¹] at hyAD
  have hg := v_gamma hv hpv hT hζ
  set g := ∑ a, u0 ω a * ζ ^ a.val with hgdef
  set c := m * ((p : C) - 1)⁻¹ with hcdef
  have hf0 : (fun x => BA x j0) ∈ AA.carrier := by
    rw [hBA]
    exact Submodule.subset_span ⟨j0, rfl⟩
  obtain ⟨s0, hs0⟩ := (AA.le_int hf0 : ∀ y, ∃ r : R, algebraMap R C r = BA y j0) 0
  have hcoef : ∀ k : ZMod p, ∃ r : R, algebraMap R C r = wt ω k * ((p : C) - 1)⁻¹ := by
    intro k
    apply hv.exists_of_le_one
    rw [map_mul, map_inv₀, hvp1, inv_one, mul_one]
    show v (ω k ^ (2 * p - 3)) ≤ 1
    rw [map_pow]
    exact pow_le_one' (valuation_le_one_of_sub_natCast_lt_one hv (ω k) k (hωcong k)) _
  choose r hr using hcoef
  have hmexp : m = ∑ b, wt ω b * BA b j0 - sS ω * BA 0 j0 := by
    rw [hmdef]
    simp [u0, sub_mul, ite_mul, Finset.sum_sub_distrib]
  have hE : (fun a => c * ω a) ∈ AA.carrier := by
    have hmem : (∑ k : ZMod p, r k • ((fun a => BA (k * a) j0) - s0 • (1 : ZMod p → C)))
        ∈ AA.carrier := by
      refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _
        (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ AA.one_mem)))
      have h := stab_lemma AA k.val (fun x => BA x j0) hf0
      simpa [ZMod.natCast_zmod_val] using h
    convert hmem using 1
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, Algebra.smul_def,
      Pi.mul_apply, Pi.algebraMap_apply, hr, hs0, mul_one]
    by_cases ha : a = 0
    · subst ha
      rw [hω0, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp [hr, hs0, Algebra.smul_def]
    · have h1' : ∑ k, wt ω k * BA (k * a) j0 = ω a * ∑ b, wt ω b * BA b j0 :=
        sum_wt_mul_comp_mul_eq hωpow hω1 hωmul a ha (fun b => BA b j0)
      have h2' : ∑ k, wt ω k = ω a * ∑ b, wt ω b := by
        simpa using sum_wt_mul_comp_mul_eq hωpow hω1 hωmul a ha (fun _ => (1 : C))
      have h3' : ∑ k, wt ω k * ((p : C) - 1)⁻¹ * (BA (k * a) j0 - BA 0 j0) =
          ((p : C) - 1)⁻¹ * ∑ k, wt ω k * BA (k * a) j0 -
            ((p : C) - 1)⁻¹ * BA 0 j0 * ∑ k, wt ω k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [h3', h1', h2', hcdef, hmexp]
      unfold sS
      ring
  have hxle : Submodule.span R (Set.range fun j x =>
      (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val) x j) ≤
      Submodule.span R (Set.range fun j x => BA x j) := by
    rw [← hBA]
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ?_)
    rw [SetLike.mem_coe]
    have h := pow_mem' AA hE j.val
    convert h using 1
    funext a
    simp [Matrix.of_apply, Pi.pow_apply]
  have hyle : Submodule.span R (Set.range fun j x =>
      (Matrix.of fun a j : ZMod p => (m⁻¹ * g * ω a) ^ j.val) x j) ≤
      Submodule.span R (Set.range fun j x => BD x j) := by
    rw [← hBD]
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ?_)
    rw [SetLike.mem_coe]
    have h := pow_mem' AD hyAD j.val
    convert h using 1
    funext a
    simp [Matrix.of_apply, Pi.pow_apply]
  have hA1 := vdet_le_of_span_le hv hxle
  have hD1 := vdet_le_of_span_le hv hyle
  have hMx := vdet_pow ω hωsep c
  have hMy := vdet_pow ω hωsep (m⁻¹ * g)
  have hcd : v c * v (m⁻¹ * g) = v g := by
    rw [hcdef, map_mul, map_mul, map_inv₀, map_inv₀, hvp1, inv_one, mul_one, ← mul_assoc,
      mul_inv_cancel₀ hvm, one_mul]
  have hN : 2 * (p * (p - 1) / 2) = p * (p - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self p).two_dvd
  have hprod : (v c ^ (p * (p - 1) / 2) * v (m⁻¹ * g) ^ (p * (p - 1) / 2)) ^ 2 =
      v (p : C) ^ p := by
    rw [← mul_pow, hcd, ← pow_mul, mul_comm (p * (p - 1) / 2) 2, hN, mul_comm p (p - 1),
      pow_mul, hg]
  have hsq : (v (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val).det *
      v (Matrix.of fun a j : ZMod p => (m⁻¹ * g * ω a) ^ j.val).det) ^ 2 =
      (v BA.det * v BD.det) ^ 2 := by
    rw [hMx, hMy, hprod, hcc]
  have hab := congrArg NNReal.sqrt hsq
  rw [NNReal.sqrt_sq, NNReal.sqrt_sq] at hab
  have hvp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr (Nat.cast_ne_zero.mpr hprime.ne_zero)
  have hαβ : v BA.det * v BD.det ≠ 0 := by
    intro h0
    rw [h0] at hcc
    exact pow_ne_zero p hvp0 (hcc.symm.trans (by norm_num))
  have haα : v (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val).det = v BA.det := by
    apply le_antisymm hA1
    have hb0 : 0 < v (Matrix.of fun a j : ZMod p => (m⁻¹ * g * ω a) ^ j.val).det := by
      refine pos_iff_ne_zero.mpr (fun h => hαβ ?_)
      rw [← hab, h, mul_zero]
    refine le_of_mul_le_mul_right ?_ hb0
    rw [hab]
    exact mul_le_mul_of_nonneg_left hD1 (by positivity)
  have hspan := hBA.trans (span_eq_of_vdet_eq hv hBAu hxle haα).symm
  have hrange : (Set.range fun j : Fin p => (fun a : ZMod p => c * ω a) ^ (j : ℕ)) =
      Set.range fun j x => (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val) x j := by
    ext F
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨finZ p j, ?_⟩
      funext a
      simp [Matrix.of_apply, finZ_val]
    · rintro ⟨j, rfl⟩
      refine ⟨⟨j.val, j.val_lt⟩, ?_⟩
      funext a
      simp [Matrix.of_apply]
  have hspanFin : AA.carrier =
      Submodule.span R (Set.range fun j : Fin p => (fun a : ZMod p => c * ω a) ^ (j : ℕ)) := by
    rw [hrange]
    exact hspan
  obtain ⟨r1, hr1⟩ := (AA.le_int hE : ∀ y, ∃ r : R, algebraMap R C r = c * ω y) 1
  simp only [hω1, mul_one] at hr1
  have hxp : (fun a : ZMod p => c * ω a) ^ p =
      fun a => algebraMap R C (r1 ^ (p - 1)) * (c * ω a) := by
    funext a
    simp only [Pi.pow_apply, map_pow, hr1]
    have hpp : c ^ p = c ^ (p - 1) * c := by
      rw [← pow_succ, Nat.sub_add_cancel hprime.one_le]
    rw [mul_pow, hωpow, hpp]
    ring
  have haug := augIdeal_eq_span_pow_of_span_pow AA.carrier (fun a : ZMod p => c * ω a) (by simp [hω0]) hspanFin
  have hsqI := sqIdeal_eq_span_of_pow_p_eq_smul (fun a : ZMod p => c * ω a) (r1 ^ (p - 1)) hxp (augIdeal AA.carrier) haug
  refine ⟨fun a => c * ω a, ω, r1 ^ (p - 1), hE, by simp [hω0], hωpow, hωcong,
    fun a => by simp only [hω1, mul_one]; ring, hxp, ?_, hspanFin, haug, hsqI, ?_⟩
  · simp only [map_pow, hr1, hω1, mul_one]
  · refine ⟨_, hspan, ?_⟩
    rw [hMx]
    simp only [hω1, mul_one]
end ReciprocityTheory.PGsh.Up
