-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.exists_family_valuation_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:49.89946+00:00
-- url     : https://prove2.me/submissions/d8ef44cd-e557-47c2-8d90-42ce1b138738

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_det_mem_and_adjugate_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_hopfOrder_exists_algebraMap_eq_of_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_hopfOrder_translate_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_cosetCoordinateMatrix_add
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_le_one_of_entries_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
private theorem hopfOrder_prod_mem_carrier (AA : HopfOrder (C := C) R N) {ι : Type} (s : Finset ι)
    (g : ι → N → C) (h : ∀ i ∈ s, g i ∈ AA.carrier) : ∏ i ∈ s, g i ∈ AA.carrier := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using AA.one_mem
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact AA.mul_mem _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
private theorem hopfOrder_const_mem (AA : HopfOrder (C := C) R N) (r : R) :
    (fun _ : N => algebraMap R C r) ∈ AA.carrier := by
  have e : (fun _ : N => algebraMap R C r) = r • (1 : N → C) := by
    funext y
    simp [Algebra.smul_def]
  rw [e]
  exact AA.carrier.smul_mem r AA.one_mem
private theorem hopfOrder_const_sub_mem (AA : HopfOrder (C := C) R N) {n : N → C} (hn : n ∈ AA.carrier)
    (z : N) : (fun y => n z - n y) ∈ AA.carrier := by
  obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA hn z
  have e : (fun y => n z - n y) = (fun _ : N => algebraMap R C r) - n := by
    funext y
    simp [hr]
  rw [e]
  exact AA.carrier.sub_mem (hopfOrder_const_mem AA r) hn
private theorem h3co_mul_add_of_coset_invariant (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (a b : N → C) (ha : ∀ y (k : K), a (y + k) = a y)
    (hb : ∀ y (k : K), b (y + k) = b y) (F F' : N → C) (y : N) :
    h3co K β (a * F + b * F') y =
      a y • h3co K β F y + b y • h3co K β F' y := by
  simp only [h3co]
  have e : (fun k : K => (a * F + b * F') (y + k)) =
      a y • (fun k : K => F (y + k)) + b y • (fun k : K => F' (y + k)) := by
    funext k
    simp [ha, hb]
  rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
private theorem h3mm_mul_add_of_coset_invariant (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (a b : N → C) (ha : ∀ y (k : K), a (y + k) = a y)
    (hb : ∀ y (k : K), b (y + k) = b y) (G G' : K → N → C) (y : N) :
    h3mm K β (fun j => a * G j + b * G' j) y =
      a y • h3mm K β G y + b y • h3mm K β G' y := by
  ext j l
  simp only [h3mm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    h3co_mul_add_of_coset_invariant K β a b ha hb, Pi.add_apply, Pi.smul_apply]
private theorem hopfOrder_det_fun_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) =
      Submodule.span R (Set.range fun j k => β k j))
    (G : K → N → C) (hG : ∀ j, G j ∈ AA.carrier) :
    (fun y => (h3mm K β G y).det) ∈ AA.carrier := by
  have h := (det_mem_and_adjugate_mem AA
    (Matrix.of fun i j => fun y => h3co K β (G i) y j)
    (fun i j => cosetCoordinates_mem AA K β hβ hAK (hG i) j)).1
  have e : ∀ y, (Matrix.of fun i j => fun y => h3co K β (G i) y j).map
      (fun g => g y) = h3mm K β G y := fun y => by
    ext i j
    rfl
  simpa only [e] using h
private theorem hopfOrder_norm_fun_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) =
      Submodule.span R (Set.range fun j k => β k j))
    (G : K → N → C) (hG : ∀ j, G j ∈ AA.carrier) :
    (fun y => ∏ k : K, (h3mm K β G (y + k)).det) ∈ AA.carrier := by
  have e : (fun y => ∏ k : K, (h3mm K β G (y + k)).det) =
      ∏ k : K, (fun y => (h3mm K β G (y + k)).det) := by
    funext y
    simp only [Finset.prod_apply]
  rw [e]
  exact hopfOrder_prod_mem_carrier AA _ _ fun k _ =>
    hopfOrder_translate_mem AA (hopfOrder_det_fun_mem AA K β hβ hAK G hG) (k : N)
private theorem valuation_sub_eq_one_of_eq_one_of_lt_one {a b : C} (ha : v a = 1) (hb : v b < 1) :
    v (a - b) = 1 := by
  have h : v (-b) < v a := by
    rw [Valuation.map_neg, ha]
    exact hb
  rw [sub_eq_add_neg, v.map_add_eq_of_lt_left h, ha]
private theorem nnreal_pow_lt_one_of_lt_one_of_ne_zero {a : NNReal} (hlt : a < 1) {m : ℕ} (hm : m ≠ 0) :
    a ^ m < 1 := by
  have h0 : (0 : NNReal) ≤ a := by positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [pow_succ]
  refine lt_of_le_of_lt (mul_le_of_le_one_left h0 ?_) hlt
  exact pow_le_one₀ h0 hlt.le
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j)) :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ x, v (h3mm K β f x).det = 1 := by
  classical
  have hlift : ∀ j : K, ∃ f ∈ AA.carrier, ∀ k : K, f k = β k j := by
    intro j
    have hmem : (fun k : K => β k j) ∈ AA.carrier.map (resK (R := R) K) := by
      rw [hAK]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.mp hmem
    exact ⟨f, hf, fun k => congrFun hfe k⟩
  choose f0 hf0 hf0e using hlift
  have hgood : ∀ x : N,
      v (h3mm K β (fun j y => f0 j (y + -x)) x).det = 1 := by
    intro x
    have e : h3mm K β (fun j y => f0 j (y + -x)) x = (β⁻¹ * β)ᵀ := by
      ext j l
      have h1 : (fun k : K => f0 j (x + (k : N) + -x)) = fun k => β k j := by
        funext k
        rw [show x + (k : N) + -x = k by abel]
        exact hf0e j k
      show (β⁻¹ *ᵥ fun k : K => f0 j (x + (k : N) + -x)) l = (β⁻¹ * β) l j
      rw [h1]
      rfl
    rw [e, Matrix.nonsing_inv_mul β hβ, Matrix.transpose_one, Matrix.det_one, map_one]
  have key : ∀ S : Finset N, ∃ G : K → N → C, (∀ j, G j ∈ AA.carrier) ∧
      ∀ z ∈ S, v (h3mm K β G z).det = 1 := by
    intro S
    refine Finset.induction_on S ⟨fun _ => 0, fun _ => AA.carrier.zero_mem, by simp⟩ ?_
    intro x S hx ih
    obtain ⟨G, hG, hS⟩ := ih
    by_cases hGx : v (h3mm K β G x).det = 1
    · refine ⟨G, hG, fun z hz => ?_⟩
      rcases Finset.mem_insert.mp hz with hzx | hz
      · rw [hzx]
        exact hGx
      · exact hS z hz
    obtain ⟨n, hn_def⟩ : ∃ n : N → C,
        n = fun y => ∏ k : K, (h3mm K β G (y + k)).det := ⟨_, rfl⟩
    have hnmem : n ∈ AA.carrier := by
      rw [hn_def]
      exact hopfOrder_norm_fun_mem AA K β hβ hAK G hG
    have hninv : ∀ y (k0 : K), n (y + k0) = n y := by
      intro y k0
      simp only [hn_def]
      exact Fintype.prod_equiv (Equiv.addLeft k0) _ _ (fun k => by simp [add_assoc])
    have hvn : ∀ y, v (n y) = v (h3mm K β G y).det ^ Fintype.card K := by
      intro y
      simp only [hn_def]
      rw [map_prod, Finset.prod_congr rfl (fun k _ =>
        valuation_det_cosetCoordinateMatrix_add hv AA K β hβ hAK G y k),
        Finset.prod_const, Finset.card_univ]
    have hDle : ∀ y, v (h3mm K β G y).det ≤ 1 := fun y =>
      valuation_det_le_one_of_entries_integral hv _ (fun i j =>
        hopfOrder_exists_algebraMap_eq_of_mem AA (cosetCoordinates_mem AA K β hβ hAK (hG i) j) y)
    have : Nonempty K := ⟨0⟩
    have hcard : Fintype.card K ≠ 0 := Fintype.card_ne_zero
    have hnS : ∀ z ∈ S, v (n z) = 1 := fun z hz => by
      rw [hvn, hS z hz, one_pow]
    have hnx : v (n x) < 1 := by
      rw [hvn]
      exact nnreal_pow_lt_one_of_lt_one_of_ne_zero (lt_of_le_of_ne (hDle x) hGx) hcard
    obtain ⟨a, ha_def⟩ : ∃ a : N → C, a = fun y => n x - n y := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : N → C, b = fun y => ∏ w ∈ S, (n w - n y) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : K → N → C, g = fun j y => f0 j (y + -x) := ⟨_, rfl⟩
    have hamem : a ∈ AA.carrier := by
      rw [ha_def]
      exact hopfOrder_const_sub_mem AA hnmem x
    have hbmem : b ∈ AA.carrier := by
      have e : (fun y => ∏ w ∈ S, (n w - n y)) = ∏ w ∈ S, (fun y => n w - n y) := by
        funext y
        simp only [Finset.prod_apply]
      rw [hb_def, e]
      exact hopfOrder_prod_mem_carrier AA S _ (fun w _ => hopfOrder_const_sub_mem AA hnmem w)
    have hgmem : ∀ j, g j ∈ AA.carrier := by
      intro j
      rw [hg_def]
      exact hopfOrder_translate_mem AA (hf0 j) (-x)
    have hgx : v (h3mm K β g x).det = 1 := by
      rw [hg_def]
      exact hgood x
    have hainv : ∀ y (k : K), a (y + k) = a y := by
      intro y k
      simp only [ha_def, hninv]
    have hbinv : ∀ y (k : K), b (y + k) = b y := by
      intro y k
      simp only [hb_def, hninv]
    refine ⟨fun j => a * G j + b * g j, fun j => AA.carrier.add_mem
      (AA.mul_mem _ _ hamem (hG j)) (AA.mul_mem _ _ hbmem (hgmem j)), fun z hz => ?_⟩
    rw [h3mm_mul_add_of_coset_invariant K β a b hainv hbinv G g z]
    rcases Finset.mem_insert.mp hz with hzx | hz
    · rw [hzx]
      have ha0 : a x = 0 := by simp only [ha_def, sub_self]
      have hb1 : v (b x) = 1 := by
        simp only [hb_def]
        rw [map_prod]
        exact Finset.prod_eq_one (fun w hw => valuation_sub_eq_one_of_eq_one_of_lt_one (hnS w hw) hnx)
      rw [ha0, zero_smul, zero_add, Matrix.det_smul, map_mul, map_pow, hgx, hb1, one_pow,
        mul_one]
    · have hb0 : b z = 0 := by
        simp only [hb_def]
        exact Finset.prod_eq_zero hz (sub_self _)
      have ha1 : v (a z) = 1 := by
        simp only [ha_def]
        rw [Valuation.map_sub_swap]
        exact valuation_sub_eq_one_of_eq_one_of_lt_one (hnS z hz) hnx
      rw [hb0, zero_smul, add_zero, Matrix.det_smul, map_mul, map_pow, hS z hz, ha1, one_pow,
        mul_one]
  obtain ⟨G, hG, hGall⟩ := key Finset.univ
  exact ⟨G, hG, fun x => hGall x (Finset.mem_univ x)⟩
end ReciprocityTheory.PGsh.L2
