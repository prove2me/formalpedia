-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_13
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:45:49.692908+00:00
-- url     : https://prove2.me/submissions/28c132b2-24c4-49c6-b06e-bd4173729768

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_capacity
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_smoothLambda
import Definitions.Def_RLCDiscrepancy_IsMonotone
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Classical

namespace RLCDiscrepancy.Dev.Disp

variable {F : Type} [Field F] [Fintype F]

def inA (T : Finset F) (x : Fin 2 → F) : Prop := x = 0 ∨ (x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)

noncomputable def mA (T : Finset F) : ℕ := (Finset.univ.filter (inA T)).card

noncomputable def alpha (T : Finset F) : ℝ :=
  (((Fintype.card F : ℝ)) ^ 2 - 2 * mA T) / (((Fintype.card F : ℝ)) ^ 2 - mA T)

noncomputable def ff (T : Finset F) (x : Fin 2 → F) : ℝ := if inA T x then 2 else alpha T

lemma inA_smul (T : Finset F) (c : F) (hc : c ≠ 0) (x : Fin 2 → F) :
    inA T (c • x) ↔ inA T x := by
  unfold inA
  simp [hc, mul_div_mul_left]

lemma card_fun2 : Fintype.card (Fin 2 → F) = Fintype.card F ^ 2 := by
  simp [Fintype.card_fun]

lemma card_B (T : Finset F) :
    (Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)).card
      = (Fintype.card F - 1) * T.card := by
  have h1 : (Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)).card
      = ((Finset.univ.filter (fun a : F => a ≠ 0)) ×ˢ T).card := by
    symm
    refine Finset.card_bij (fun p _ => ![p.1, p.1 * p.2]) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      simp [hp.1, mul_div_cancel_left₀ _ hp.1, hp.2]
    · intro p hp p' hp' h
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      rw [← h0] at h1
      exact Prod.ext h0 (mul_left_cancel₀ hp.1 h1)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨(x 0, x 1 / x 0), ?_, ?_⟩
      · simp [hx.1, hx.2]
      · ext i; fin_cases i <;> simp [mul_div_cancel₀ _ hx.1]
  rw [h1, Finset.card_product]
  congr 1
  have : (Finset.univ.filter (fun a : F => a ≠ 0)) = Finset.univ.erase 0 := by
    ext a; simp
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

lemma mA_eq (T : Finset F) : mA T = 1 + (Fintype.card F - 1) * T.card := by
  unfold mA
  have : Finset.univ.filter (inA T) =
      insert 0 (Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)) := by
    ext x
    simp only [inA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [this, Finset.card_insert_of_notMem, card_B]
  · ring
  · simp

def phi (a : F) (x : Fin 2 → F) : F := x 1 - a * x 0

noncomputable def Sr (T : Finset F) (a r : F) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => phi a x = r), ff T x

section hyp
variable (T : Finset F) (hm : 2 * (mA T : ℝ) ≤ (Fintype.card F : ℝ) ^ 2)

lemma mA_pos : 0 < mA T := by
  unfold mA
  apply Finset.card_pos.2
  exact ⟨0, by simp [inA]⟩

include hm in
lemma alpha_nonneg : 0 ≤ alpha T := by
  have h1 : (1:ℝ) ≤ mA T := by exact_mod_cast mA_pos T
  unfold alpha
  apply div_nonneg <;> linarith

include hm in
lemma alpha_le_one : alpha T ≤ 1 := by
  have h1 : (1:ℝ) ≤ mA T := by exact_mod_cast mA_pos T
  unfold alpha
  rw [div_le_one (by linarith)]
  linarith

include hm in
lemma ff_nonneg (x : Fin 2 → F) : 0 ≤ ff T x := by
  unfold ff
  split_ifs
  · norm_num
  · exact alpha_nonneg T hm

include hm in
lemma ff_le_two (x : Fin 2 → F) : ff T x ≤ 2 := by
  unfold ff
  split_ifs
  · norm_num
  · linarith [alpha_le_one T hm]

include hm in
lemma sum_ff : ∑ x, ff T x = (Fintype.card F : ℝ) ^ 2 := by
  have h1 : (1:ℝ) ≤ mA T := by exact_mod_cast mA_pos T
  have hden : (Fintype.card F : ℝ) ^ 2 - mA T ≠ 0 := by linarith
  have hle : mA T ≤ Fintype.card F ^ 2 := by
    have := Finset.card_le_univ (Finset.univ.filter (inA T))
    rwa [card_fun2] at this
  have hc : (Finset.univ.filter (fun x => ¬ inA T x)).card = Fintype.card F ^ 2 - mA T := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 2 → F))) (inA T)
    rw [Finset.card_univ, card_fun2] at this
    unfold mA
    omega
  have e1 : ∑ x ∈ Finset.univ.filter (inA T), ff T x = 2 * (mA T : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (2:ℝ)) (fun x hx => by
      have := (Finset.mem_filter.1 hx).2
      simp [ff, this])]
    simp [mA]; ring
  have e2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ inA T x), ff T x
      = ((Fintype.card F : ℝ) ^ 2 - mA T) * alpha T := by
    rw [Finset.sum_congr rfl (g := fun _ => alpha T) (fun x hx => by
      have := (Finset.mem_filter.1 hx).2
      simp [ff, this])]
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    rw [Nat.cast_sub hle]; push_cast; ring
  have : ∑ x, ff T x = 2 * (mA T : ℝ) + alpha T * ((Fintype.card F : ℝ) ^ 2 - mA T) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (inA T), e1, e2]; ring
  rw [this]
  unfold alpha
  field_simp
  ring

lemma card_fiber (a r : F) :
    (Finset.univ.filter (fun x : Fin 2 → F => phi a x = r)).card = Fintype.card F := by
  have : Finset.univ.filter (fun x : Fin 2 → F => phi a x = r)
      = Finset.univ.image (fun c : F => (![c, a * c + r] : Fin 2 → F)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have h' : x 1 - a * x 0 = r := h
      refine ⟨x 0, ?_⟩
      ext i; fin_cases i
      · simp
      · simp; linear_combination -h'
    · rintro ⟨c, rfl⟩
      show (![c, a * c + r] : Fin 2 → F) 1 - a * (![c, a * c + r] : Fin 2 → F) 0 = r
      simp
  rw [this, Finset.card_image_of_injective, Finset.card_univ]
  intro c c' h
  simpa using congrFun h 0

lemma phi_sub (a : F) (x c : Fin 2 → F) : phi a (x - c) = phi a x - phi a c := by
  simp [phi]; ring

lemma phi_smul (a r : F) (x : Fin 2 → F) : phi a (r • x) = r * phi a x := by
  simp [phi]; ring

include hm in
lemma Sr_zero (a : F) (ha : a ∈ T) : Sr T a 0 = 2 * Fintype.card F := by
  unfold Sr
  rw [Finset.sum_congr rfl (g := fun _ => (2:ℝ))]
  · simp [card_fiber]; ring
  · intro x hx
    have h := (Finset.mem_filter.1 hx).2
    have : inA T x := by
      unfold inA
      by_cases h0 : x 0 = 0
      · left
        ext i; fin_cases i
        · simpa using h0
        · simp [phi, h0] at h; simpa using h
      · right
        refine ⟨h0, ?_⟩
        have : x 1 = a * x 0 := by simp [phi] at h; linear_combination h
        rw [this, mul_div_cancel_right₀ _ h0]; exact ha
    simp [ff, this]

include hm in
lemma Sr_smul (a r : F) (hr : r ≠ 0) : Sr T a r = Sr T a 1 := by
  unfold Sr
  refine Finset.sum_nbij' (fun x => r⁻¹ • x) (fun x => r • x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [phi_smul, hx]; field_simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [phi_smul, hx]; simp
  · intro x hx; simp [hr]
  · intro x hx; simp [hr]
  · intro x hx
    have : ff T (r⁻¹ • x) = ff T x := by
      unfold ff
      simp only [inA_smul T r⁻¹ (inv_ne_zero hr)]
    exact this.symm

include hm in
lemma sum_Sr (a : F) : ∑ r, Sr T a r = (Fintype.card F : ℝ) ^ 2 := by
  unfold Sr
  rw [Finset.sum_fiberwise Finset.univ (phi a) (ff T)]
  exact sum_ff T hm

lemma sum_conv (T : Finset F) (a : F) :
    ∑ c ∈ Finset.univ.filter (fun x : Fin 2 → F => phi a x = 0), ∑ x, ff T x * ff T (x - c)
      = ∑ r, Sr T a r ^ 2 := by
  rw [Finset.sum_comm]
  have h1 : ∀ x : Fin 2 → F, ∑ c ∈ Finset.univ.filter (fun x : Fin 2 → F => phi a x = 0),
      ff T x * ff T (x - c) = ff T x * Sr T a (phi a x) := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    unfold Sr
    refine Finset.sum_nbij' (fun c => x - c) (fun y => x - y) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rw [phi_sub, hc, sub_zero]
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [phi_sub, hy, sub_self]
    · intro c hc; simp
    · intro c hc; simp
    · intro c hc; rfl
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [← Finset.sum_fiberwise Finset.univ (phi a) (fun x => ff T x * Sr T a (phi a x))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_congr rfl (g := fun x => ff T x * Sr T a r)
    (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
  rw [← Finset.sum_mul]
  rw [sq]; rfl

end hyp

open RLCDiscrepancy

lemma consSeq_zero (u : Fin 1 → Fin 2 → F) : consSeq u 0 = ⊥ := by
  unfold consSeq; simp

lemma consSeq_one (u : Fin 1 → Fin 2 → F) : consSeq u 1 = Submodule.span F {u 0} := by
  unfold consSeq
  congr 1
  ext x
  simp [Fin.fin_one_eq_zero]

lemma relDev_bot (g : (Fin 2 → F) → ℝ) : relDev (⊥ : Submodule F (Fin 2 → F)) g = g 0 - 1 := by
  have : codeFinset (⊥ : Submodule F (Fin 2 → F)) = {0} := by
    ext x; simp
  unfold relDev
  rw [this]; simp

lemma codeFinset_span (v : Fin 2 → F) (hv : v 0 ≠ 0) :
    codeFinset (Submodule.span F {v}) =
      Finset.univ.filter (fun x : Fin 2 → F => phi (v 1 / v 0) x = 0) := by
  ext x
  rw [mem_codeFinset, Submodule.mem_span_singleton]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    show (c • v) 1 - v 1 / v 0 * (c • v) 0 = 0
    simp; field_simp; ring
  · intro h
    have h' : x 1 - v 1 / v 0 * x 0 = 0 := h
    refine ⟨x 0 / v 0, ?_⟩
    ext i; fin_cases i
    · simp; field_simp
    · simp
      have : x 1 = v 1 / v 0 * x 0 := by linear_combination h'
      rw [this]; field_simp

section hyp2
variable (T : Finset F) (hm : 2 * (mA T : ℝ) ≤ (Fintype.card F : ℝ) ^ 2)

include hm in
lemma relDev_line (v : Fin 2 → F) (hv : v 0 ≠ 0 ∧ v 1 / v 0 ∈ T) :
    relDev (Submodule.span F {v}) (ff T) = 1 := by
  unfold relDev
  rw [codeFinset_span v hv.1, card_fiber]
  have := Sr_zero T hm (v 1 / v 0) hv.2
  unfold Sr at this
  rw [this]
  have : (Fintype.card F : ℝ) ≠ 0 := by positivity
  field_simp; norm_num

include hm in
lemma relDev_line_F (hq : 2 ≤ Fintype.card F) (v : Fin 2 → F) (hv : v 0 ≠ 0 ∧ v 1 / v 0 ∈ T) :
    relDev (Submodule.span F {v}) (selfConv (ff T)) = 1 / ((Fintype.card F : ℝ) - 1) := by
  have hq' : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  set a := v 1 / v 0 with ha
  unfold relDev
  rw [codeFinset_span v hv.1, card_fiber]
  unfold selfConv
  rw [← Finset.sum_div, sum_conv]
  have h0 := Sr_zero T hm a hv.2
  have hsum := sum_Sr T hm a
  have hsplit : ∀ g : F → ℝ, ∑ r, g r = g 0 + ∑ r ∈ Finset.univ.erase 0, g r := fun g =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have hcard : ((Finset.univ : Finset F).erase 0).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [hsplit] at hsum
  rw [hsplit (fun r => Sr T a r ^ 2)]
  rw [Finset.sum_congr rfl (g := fun _ => Sr T a 1)
      (fun r hr => Sr_smul T hm a r (Finset.ne_of_mem_erase hr))] at hsum
  rw [Finset.sum_congr rfl (g := fun _ => Sr T a 1 ^ 2)
      (fun r hr => by rw [Sr_smul T hm a r (Finset.ne_of_mem_erase hr)])]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hsum ⊢
  rw [Nat.cast_sub (by omega)] at hsum ⊢
  rw [h0] at hsum ⊢
  push_cast at hsum ⊢
  set q : ℝ := ((Fintype.card F : ℕ) : ℝ) with hqdef
  set σ := Sr T a 1
  have hq1 : q - 1 ≠ 0 := by linarith
  have hσ : σ = q * (q - 2) / (q - 1) := by
    rw [eq_div_iff hq1]; linear_combination hsum
  have hq0 : q ≠ 0 := by linarith
  rw [hσ]
  field_simp
  ring

end hyp2

section fin
variable (T : Finset F) (hm : 2 * (mA T : ℝ) ≤ (Fintype.card F : ℝ) ^ 2)

include hm in
lemma supNorm_le : supNorm (ff T) ≤ 2 := by
  unfold supNorm
  apply Finset.sup'_le
  intro x _
  rw [abs_of_nonneg (ff_nonneg T hm x)]
  exact ff_le_two T hm x

include hm in
lemma gamma_lt (hq : (Fintype.card F : ℝ) = 2 ^ 100) :
    (Fintype.card F : ℝ) ^ (2 / 5 : ℝ) * smoothLambda (ff T) 1 (4 / Fintype.card F) < 1 := by
  have hs := supNorm_le T hm
  have hLam : smoothLambda (ff T) 1 (4 / Fintype.card F) ≤ 1 / 2 ^ 49 := by
    unfold smoothLambda
    rw [hq]
    apply max_le
    · have h0 : 0 ≤ supNorm (ff T) := by
        unfold supNorm
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun x => |ff T x|) (Finset.mem_univ 0))
      calc supNorm (ff T) * (((2:ℝ) ^ 100) ^ 1)⁻¹ ≤ 2 * (((2:ℝ) ^ 100) ^ 1)⁻¹ := by gcongr
        _ ≤ 1 / 2 ^ 49 := by norm_num
    · rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · norm_num
  have hp : ((2:ℝ) ^ 100) ^ ((2:ℝ) / 5) = 2 ^ 40 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hl0 : 0 ≤ smoothLambda (ff T) 1 (4 / Fintype.card F) := by
    unfold smoothLambda
    exact le_trans (Real.sqrt_nonneg _) (le_max_right _ _)
  rw [hq, hp]
  calc (2:ℝ) ^ 40 * smoothLambda (ff T) 1 (4 / ((2:ℝ) ^ 100)) ≤ 2 ^ 40 * (1 / 2 ^ 49) := by
        rw [hq] at hLam; gcongr
    _ < 1 := by norm_num

def Ev (T : Finset F) (u : Fin 1 → Fin 2 → F) : Prop :=
  IsSmooth u (selfConv (ff T)) (4 / Fintype.card F) 1 ∧
    IsMonotone u (ff T) ((Fintype.card F : ℝ) ^ (2 / 5 : ℝ) * smoothLambda (ff T) 1 (4 / Fintype.card F)) ∧
      ¬ IsSmooth u (ff T) ((Fintype.card F : ℝ) ^ (2 / 5 : ℝ) * smoothLambda (ff T) 1 (4 / Fintype.card F)) 1

include hm in
lemma ev_of (hq : (Fintype.card F : ℝ) = 2 ^ 100) (u : Fin 1 → Fin 2 → F)
    (hu : u 0 0 ≠ 0 ∧ u 0 1 / u 0 0 ∈ T) : Ev T u := by
  have hq2 : 2 ≤ Fintype.card F := by
    have : (2:ℝ) ≤ Fintype.card F := by rw [hq]; norm_num
    exact_mod_cast this
  have hqpos : (0:ℝ) < Fintype.card F := by rw [hq]; norm_num
  have h0 : ff T 0 = 2 := by simp [ff, inA]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · rw [consSeq_zero, relDev_bot]
      simp only [Nat.sub_zero, pow_one]
      unfold selfConv
      have hn : 0 ≤ (∑ x, ff T x * ff T (x - 0)) := Finset.sum_nonneg (fun x _ =>
        mul_nonneg (ff_nonneg T hm x) (ff_nonneg T hm _))
      have hu2 : (∑ x, ff T x * ff T (x - 0)) ≤ 2 * (Fintype.card F : ℝ) ^ 2 := by
        calc (∑ x, ff T x * ff T (x - 0)) ≤ ∑ x, 2 * ff T x := Finset.sum_le_sum (fun x _ =>
              mul_le_mul_of_nonneg_right (by simpa using ff_le_two T hm x) (ff_nonneg T hm x) |>.trans_eq' rfl |> fun h => by nlinarith [ff_le_two T hm (x - 0), ff_nonneg T hm x, ff_nonneg T hm (x - 0)])
          _ = 2 * (Fintype.card F : ℝ) ^ 2 := by rw [← Finset.mul_sum, sum_ff T hm]
      have hd : (0:ℝ) < (Fintype.card F : ℝ) ^ 2 := by positivity
      rw [abs_le]
      constructor
      · have : 0 ≤ (∑ x, ff T x * ff T (x - 0)) / (Fintype.card F : ℝ) ^ 2 := by positivity
        have h4 : (Fintype.card F : ℝ) * (4 / Fintype.card F) = 4 := by field_simp
        linarith
      · have : (∑ x, ff T x * ff T (x - 0)) / (Fintype.card F : ℝ) ^ 2 ≤ 2 := by
          rw [div_le_iff₀ hd]; linarith
        have h4 : (Fintype.card F : ℝ) * (4 / Fintype.card F) = 4 := by field_simp
        linarith
    · rw [consSeq_one, relDev_line_F T hm hq2 _ hu]
      simp only [Nat.sub_self, pow_zero, one_mul]
      have hq2' : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast hq2
      rw [abs_of_pos (by apply div_pos <;> linarith), div_le_div_iff₀ (by linarith) hqpos]
      linarith
  · intro j hj1 hjk _
    obtain rfl : j = 1 := by omega
    rw [consSeq_one, show (1 - 1 = 0) from rfl, consSeq_zero, relDev_bot, relDev_line T hm _ hu, h0]
    norm_num
  · intro h
    have := h 1 le_rfl
    rw [consSeq_one, relDev_line T hm _ hu] at this
    simp only [Nat.sub_self, pow_zero, one_mul, abs_one] at this
    linarith [gamma_lt T hm hq]

end fin

lemma prob_ge (P : (Fin 1 → Fin 2 → F) → Prop) (T : Finset F)
    (h : ∀ u : Fin 1 → Fin 2 → F, (u 0 0 ≠ 0 ∧ u 0 1 / u 0 0 ∈ T) → P u) :
    ((Fintype.card F - 1 : ℕ) * T.card : ℝ) / (Fintype.card F : ℝ) ^ 2 ≤ PunctSketch.coinProb P := by
  unfold PunctSketch.coinProb
  have hcard : Fintype.card (Fin 1 → Fin 2 → F) = Fintype.card F ^ 2 := by
    simp [Fintype.card_fun]
  rw [hcard]
  push_cast
  have hB := card_B T
  have hle : (Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)).card ≤
      (Finset.univ.filter P).card := by
    have : (Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)).card =
        ((Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)).image
          (fun x : Fin 2 → F => (fun _ : Fin 1 => x))).card := by
      rw [Finset.card_image_of_injective]
      intro x y hxy
      exact congrFun hxy 0
    rw [this]
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨x, hx, rfl⟩ := hu
    exact h _ hx
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have h2 : (((Fintype.card F - 1 : ℕ) : ℝ) * T.card) ≤ ((Finset.univ.filter P).card : ℝ) := by
    have : (Finset.univ.filter (fun x : Fin 2 → F => x 0 ≠ 0 ∧ x 1 / x 0 ∈ T)).card
        ≤ (Finset.univ.filter P).card := hle
    rw [hB] at this
    exact_mod_cast this
  have hpos : (0:ℝ) < (Fintype.card F : ℝ) ^ 2 := by
    have : (0:ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  apply div_le_div_of_nonneg_right _ hpos.le
  exact_mod_cast h2

end RLCDiscrepancy.Dev.Disp

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.Disp

theorem lemma_4_13_disproof : ¬ (∀ (F : Type) [Field F] [Fintype F] (n k : ℕ) (hkn : k ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ)
    (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k),
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          IsMonotone u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2)) := by
  intro H
  letI : Fintype (GaloisField 2 100) := Fintype.ofFinite _
  have hq : (Fintype.card (GaloisField 2 100) : ℝ) = 2 ^ 100 := by
    have : Fintype.card (GaloisField 2 100) = 2 ^ 100 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 100 (by norm_num)]
    rw [this]; norm_num
  have hqn : Fintype.card (GaloisField 2 100) = 2 ^ 100 := by exact_mod_cast hq
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (GaloisField 2 100))) (n := 2 ^ 99 - 1)
    (by rw [Finset.card_univ, hqn]; omega)
  have hm : 2 * (mA T : ℝ) ≤ (Fintype.card (GaloisField 2 100) : ℝ) ^ 2 := by
    rw [mA_eq, hqn, hT]
    have : 1 ≤ 2 ^ 99 := Nat.one_le_two_pow
    push_cast [Nat.cast_sub this]
    norm_num
  have hf : IsNormalized (ff T) := ⟨ff_nonneg T hm, by simpa using sum_ff T hm⟩
  have hΓ : (0:ℝ) < 4 / (Fintype.card (GaloisField 2 100) : ℝ) := by rw [hq]; norm_num
  have ht : 20 * Real.logb (Fintype.card (GaloisField 2 100) : ℝ) ((2:ℕ) : ℝ) ≤ 2 / 5 := by
    rw [hq]
    unfold Real.logb
    rw [Real.log_pow]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    push_cast
    rw [show (20:ℝ) * (Real.log 2 / (100 * Real.log 2)) = 1 / 5 by field_simp; norm_num]
    norm_num
  have h := H (GaloisField 2 100) 2 1 (by norm_num) (ff T) hf _ hΓ (2 / 5) ht (by norm_num)
  have hlow := prob_ge (Ev T) T (fun u hu => ev_of T hm hq u hu)
  have h' := hlow.trans h
  rw [hqn, hT] at h'
  have e1 : ((2:ℝ) ^ 100) ^ (-(1 / 10 : ℝ) * (2 / 5 : ℝ) ^ 2) < 2 / 5 := by
    have hy : ((2:ℝ) ^ 100) ^ ((2:ℝ) / 125) = 2 ^ ((8:ℝ) / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hy5 : (((2:ℝ) ^ ((8:ℝ) / 5)) ^ 5) = 2 ^ 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hy1 : (5 / 2 : ℝ) < 2 ^ ((8:ℝ) / 5) := by
      by_contra hc
      push_neg at hc
      have := pow_le_pow_left₀ (by positivity) hc 5
      rw [hy5] at this
      norm_num at this
    have : -(1 / 10 : ℝ) * (2 / 5 : ℝ) ^ 2 = -((2:ℝ) / 125) := by norm_num
    rw [this, Real.rpow_neg (by positivity), hy]
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]
    linarith
  have e2 : (2:ℝ) / 5 ≤ (((2 ^ 100 - 1 : ℕ) : ℝ) * ((2 ^ 99 - 1 : ℕ) : ℝ)) / ((2:ℕ) ^ 100 : ℝ) ^ 2 := by
    have h1 : 1 ≤ 2 ^ 100 := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ 99 := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    norm_num
  push_cast at h' e2 ⊢
  linarith
end RLCDiscrepancy

theorem solution : type_of% @RLCDiscrepancy.lemma_4_13_disproof := @RLCDiscrepancy.lemma_4_13_disproof
