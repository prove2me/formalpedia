-- Prove2me | solution 1 for TranspositionIID.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:45:04.151679+00:00
-- url     : https://prove2.me/submissions/d9ee8328-b89e-44ae-8579-e810d047e2b2

import Mathlib
import Definitions.Def_TranspositionIID_Main_Buffer
import Theorems.Thm_TranspositionIID_Main_lemma_2_1

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L21
open TranspositionIID.Main Set

variable {n : ℕ}

noncomputable def Phi (p : Fin n → ℝ) (x r : ℝ) : ℝ := ∑ i, max (r - |x - Real.log (p i)|) 0

def Sset (p : Fin n → ℝ) (x : ℝ) : Set ℝ := {r | 0 ≤ r ∧ 1 ≤ Phi p x r}

lemma root_eq (p : Fin n → ℝ) (x : ℝ) : bufferRoot p x = sInf (Sset p x) := rfl

lemma Phi_cont (p : Fin n → ℝ) (x : ℝ) : Continuous (Phi p x) := by
  unfold Phi; fun_prop

lemma Phi_zero (p : Fin n → ℝ) (x : ℝ) : Phi p x 0 = 0 := by
  unfold Phi
  apply Finset.sum_eq_zero; intro i _
  apply max_eq_right; linarith [abs_nonneg (x - Real.log (p i))]

lemma Phi_le (p : Fin n → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) : Phi p x r ≤ n * r := by
  unfold Phi
  calc ∑ i, max (r - |x - Real.log (p i)|) 0 ≤ ∑ _i : Fin n, r :=
        Finset.sum_le_sum fun i _ => max_le (by linarith [abs_nonneg (x - Real.log (p i))]) hr
    _ = n * r := by simp

lemma Phi_ge (p : Fin n → ℝ) (x : ℝ) (i0 : Fin n) (r : ℝ) :
    r - |x - Real.log (p i0)| ≤ Phi p x r := by
  unfold Phi
  exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (r - |x - Real.log (p i)|) 0)
    (fun i _ => le_max_right _ _) (Finset.mem_univ i0))

lemma Sset_nonempty (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : (Sset p x).Nonempty := by
  refine ⟨1 + |x - Real.log (p ⟨0, hn⟩)|, by positivity, ?_⟩
  have := Phi_ge p x ⟨0, hn⟩ (1 + |x - Real.log (p ⟨0, hn⟩)|)
  linarith

lemma Sset_closed (p : Fin n → ℝ) (x : ℝ) : IsClosed (Sset p x) :=
  isClosed_Ici.inter (isClosed_le continuous_const (Phi_cont p x))

lemma Sset_bdd (p : Fin n → ℝ) (x : ℝ) : BddBelow (Sset p x) := ⟨0, fun r hr => hr.1⟩

lemma root_le (p : Fin n → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) (h : 1 ≤ Phi p x r) :
    bufferRoot p x ≤ r := csInf_le (Sset_bdd p x) ⟨hr, h⟩

lemma root_spec (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) :
    0 < bufferRoot p x ∧ Phi p x (bufferRoot p x) = 1 := by
  have hmem := (Sset_closed p x).csInf_mem (Sset_nonempty hn p x) (Sset_bdd p x)
  rw [← root_eq] at hmem
  obtain ⟨hR0, h1⟩ := hmem
  set R := bufferRoot p x with hR
  have hivt := intermediate_value_Icc hR0 (Phi_cont p x).continuousOn
  have h1mem : (1 : ℝ) ∈ Icc (Phi p x 0) (Phi p x R) := by
    rw [Phi_zero]; exact ⟨zero_le_one, h1⟩
  obtain ⟨r, hr, hr1⟩ := hivt h1mem
  have hRr : R ≤ r := root_le p x hr.1 (by rw [hr1])
  have hrR : r = R := le_antisymm hr.2 hRr
  have hPhi : Phi p x R = 1 := by rw [← hrR]; exact hr1
  refine ⟨lt_of_le_of_ne hR0 (fun h0 => ?_), hPhi⟩
  rw [← h0, Phi_zero] at hPhi; norm_num at hPhi

lemma buffer_le (p : Fin n → ℝ) (x : ℝ) : buffer p x ≤ 1 / 2 := by
  unfold buffer; have := min_le_left 1 (bufferRoot p x); linarith

lemma buffer_ge (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : 1 / (2 * (n : ℝ)) ≤ buffer p x := by
  obtain ⟨hR0, hPhi⟩ := root_spec hn p x
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ (n : ℝ) * bufferRoot p x := by
    have := Phi_le p x hR0.le; linarith
  have h2 : 1 / (n : ℝ) ≤ bufferRoot p x := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 1 / (n : ℝ) ≤ min 1 (bufferRoot p x) := by
    apply le_min _ h2
    rw [div_le_one (by linarith)]; exact hn'
  unfold buffer
  calc 1 / (2 * (n : ℝ)) = 1 / 2 * (1 / (n : ℝ)) := by field_simp
    _ ≤ 1 / 2 * min 1 (bufferRoot p x) := mul_le_mul_of_nonneg_left h3 (by norm_num)

lemma buffer_pos (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : 0 < buffer p x := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (buffer_ge hn p x)

end TranspositionIID.Main.Dev.L21
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L22
open TranspositionIID.Main

variable {n : ℕ}

lemma pos_count (σ : ListState n) (i : Fin n) :
    (∑ j, (if σ j < σ i then (1 : ℝ) else 0)) = ((σ i).val : ℝ) := by
  rw [Equiv.sum_comp σ (fun k => if k < σ i then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun k : Fin n => k < σ i)) = Finset.Iio (σ i) := by
    ext k; simp
  rw [this, Fin.card_Iio]

lemma cost_eq (p : Fin n → ℝ) (σ : ListState n) :
    cost p σ = ∑ i, p i * (∑ j, (if σ j < σ i then (1 : ℝ) else 0) + 1) := by
  unfold cost
  apply Finset.sum_congr rfl; intro i _
  rw [pos_count]; push_cast; ring

noncomputable def uu (σ : ListState n) (i j : Fin n) : ℝ :=
  (if σ j < σ i then (1 : ℝ) else 0) - (if j < i then (1 : ℝ) else 0)

lemma uu_anti (σ : ListState n) (i j : Fin n) : uu σ j i = - uu σ i j := by
  unfold uu
  rcases lt_trichotomy i j with h | rfl | h
  · rcases lt_trichotomy (σ i) (σ j) with h' | h' | h'
    · simp [h, h', not_lt.2 h'.le, not_lt.2 h.le]
    · exact absurd (σ.injective h') h.ne
    · simp [h, h', not_lt.2 h'.le, not_lt.2 h.le]
  · simp
  · rcases lt_trichotomy (σ i) (σ j) with h' | h' | h'
    · simp [h, h', not_lt.2 h'.le, not_lt.2 h.le]
    · exact absurd (σ.injective h') h.ne'
    · simp [h, h', not_lt.2 h'.le, not_lt.2 h.le]

lemma cost_one_eq (p : Fin n → ℝ) :
    cost p 1 = ∑ i, p i * (∑ j, (if j < i then (1 : ℝ) else 0) + 1) := by
  unfold cost
  apply Finset.sum_congr rfl; intro i _
  have : (∑ j, (if j < i then (1 : ℝ) else 0)) = (i.val : ℝ) := by
    rw [Finset.sum_boole]
    have : (Finset.univ.filter (fun k : Fin n => k < i)) = Finset.Iio i := by
      ext k; simp
    rw [this, Fin.card_Iio]
  rw [this]; simp

lemma cost_diff (p : Fin n → ℝ) (σ : ListState n) :
    cost p σ - cost p 1 = ∑ i, ∑ j, p i * uu σ i j := by
  rw [cost_eq, cost_one_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  have hu : (∑ j, (if σ j < σ i then (1 : ℝ) else 0) + 1) -
      (∑ j, (if j < i then (1 : ℝ) else 0) + 1) = ∑ j, uu σ i j := by
    simp only [uu, Finset.sum_sub_distrib]; ring
  rw [← mul_sub, hu, Finset.mul_sum]

lemma sym_reduce (p : Fin n → ℝ) (σ : ListState n) :
    ∑ i, ∑ j, p i * uu σ i j =
      ∑ i, ∑ j, (if p j < p i then (p i - p j) * uu σ i j else 0) := by
  set S := ∑ i, ∑ j, p i * uu σ i j with hS
  have h1 : S = ∑ i, ∑ j, - (p j * uu σ i j) := by
    rw [hS, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [uu_anti]; ring
  have h2 : 2 * S = ∑ i, ∑ j, (p i - p j) * uu σ i j := by
    have : S + S = ∑ i, ∑ j, p i * uu σ i j + ∑ i, ∑ j, - (p j * uu σ i j) := by
      linarith [hS, h1]
    rw [two_mul, this, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  set v : Fin n → Fin n → ℝ := fun i j => (p i - p j) * uu σ i j with hv
  have hvs : ∀ i j, v j i = v i j := by
    intro i j; simp only [hv]; rw [uu_anti]; ring
  have hsplit : ∀ i j, v i j = (if p j < p i then v i j else 0) + (if p i < p j then v i j else 0) := by
    intro i j
    rcases lt_trichotomy (p j) (p i) with h | h | h
    · simp [h, not_lt.2 h.le]
    · simp [hv, h]
    · simp [h, not_lt.2 h.le]
  have h3 : ∑ i, ∑ j, v i j = 2 * ∑ i, ∑ j, (if p j < p i then v i j else 0) := by
    have e1 : ∑ i, ∑ j, v i j = ∑ i, ∑ j, ((if p j < p i then v i j else 0) +
        (if p i < p j then v i j else 0)) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    rw [e1]
    simp only [Finset.sum_add_distrib]
    have e2 : ∑ i, ∑ j, (if p i < p j then v i j else 0) = ∑ i, ∑ j, (if p j < p i then v i j else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hvs]
    rw [e2]; ring
  have : 2 * S = 2 * ∑ i, ∑ j, (if p j < p i then v i j else 0) := by rw [h2]; exact h3
  linarith

noncomputable def Aσ (p : Fin n → ℝ) (σ : ListState n) : ℝ :=
  ∑ i, ∑ j, (if p j < p i ∧ σ j < σ i then p i - p j else 0)

lemma cost_diff_A (p : Fin n → ℝ) (hsort : Antitone p) (σ : ListState n) :
    cost p σ - cost p 1 = Aσ p σ := by
  rw [cost_diff, sym_reduce]
  unfold Aσ
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases h : p j < p i
  · have hji : ¬ (j < i) := fun hlt => absurd (hsort hlt.le) (not_le.2 h)
    simp only [h, if_true, uu, hji, if_false, sub_zero, true_and]
    split_ifs <;> simp
  · simp [h]

lemma Aσ_nonneg (p : Fin n → ℝ) (σ : ListState n) : 0 ≤ Aσ p σ := by
  unfold Aσ
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  split_ifs with h
  · linarith [h.1]
  · exact le_rfl

lemma excess_eq_A (p : Fin n → ℝ) (hsort : Antitone p) (σ : ListState n) :
    excess p σ = Aσ p σ := by
  have hopt : optimum p = cost p 1 := by
    unfold optimum
    apply le_antisymm (csInf_le (Set.finite_range _).bddBelow ⟨1, rfl⟩)
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨τ, rfl⟩
    have := cost_diff_A p hsort τ
    have := Aσ_nonneg p τ
    linarith
  unfold excess
  rw [hopt]; exact cost_diff_A p hsort σ

end TranspositionIID.Main.Dev.L22
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L22
open TranspositionIID.Main TranspositionIID.Main.Dev.L21 Set

variable {n : ℕ}

lemma A_scalar (yi yj θb : ℝ) (h1 : yj ≤ yi) (h2 : yi - yj ≤ 2 * θb) :
    Real.exp yi - Real.exp yj ≤ 2 * θb * Real.exp yi := by
  have h3 : Real.exp yj = Real.exp yi * Real.exp (yj - yi) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 := Real.add_one_le_exp (yj - yi)
  have h5 := Real.exp_pos yi
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h4 h5.le]

lemma B_scalar (b θ yi yj : ℝ) (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hyi : yi = b + θ)
    (hyj : yj < b - θ) :
    Real.exp yi - Real.exp yj ≤ (1 + Real.sqrt (Real.exp 1)) * (Real.exp b - Real.exp yj) := by
  set a := Real.exp b with ha
  set E := Real.exp θ with hE
  set c := Real.exp yj with hc
  set s := Real.sqrt (Real.exp 1) with hs
  have ha0 : 0 < a := Real.exp_pos _
  have hc0 : 0 < c := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp hθ0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hEs : E ≤ s := by
    have : E ^ 2 ≤ Real.exp 1 := by
      rw [hE, ← Real.exp_nat_mul]; apply Real.exp_le_exp.2; push_cast; linarith
    calc E = Real.sqrt (E ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ s := Real.sqrt_le_sqrt this
  have hyi' : Real.exp yi = a * E := by rw [hyi, Real.exp_add]
  have hcE : c * E ≤ a := by
    rw [hc, hE, ← Real.exp_add]; apply Real.exp_le_exp.2; linarith
  rw [hyi']
  have k1 : s * (c * E) ≤ s * a := mul_le_mul_of_nonneg_left hcE hs0
  have k2 : s * a ≤ a * (E * (1 + s - E)) := by
    have := mul_nonneg ha0.le (mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hEs))
    nlinarith
  have k3 : s * c ≤ a * (1 + s - E) := by
    have hE0 : 0 < E := by linarith
    have : E * (s * c) ≤ E * (a * (1 + s - E)) := by nlinarith
    exact le_of_mul_le_mul_left this hE0
  nlinarith

lemma count_near (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) :
    ((Finset.univ.filter (fun j : Fin n => |Real.log (p j) - x| ≤ buffer p x)).card : ℝ) *
      buffer p x ≤ 1 := by
  set θ := buffer p x with hθ
  have hθp : 0 < θ := buffer_pos hn p x
  obtain ⟨hR0, hPhi⟩ := root_spec hn p x
  have h2θ : 2 * θ ≤ bufferRoot p x := by
    rw [hθ]; unfold buffer
    have := min_le_right 1 (bufferRoot p x)
    linarith
  have hsum : ∑ j, max (2 * θ - |x - Real.log (p j)|) 0 ≤ 1 := by
    rw [← hPhi]; unfold Phi
    exact Finset.sum_le_sum fun j _ => max_le_max (by linarith) le_rfl
  have hsub : ∑ j ∈ Finset.univ.filter (fun j : Fin n => |Real.log (p j) - x| ≤ θ), θ ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => |Real.log (p j) - x| ≤ θ),
        max (2 * θ - |x - Real.log (p j)|) 0 := by
    apply Finset.sum_le_sum; intro j hj
    have := (Finset.mem_filter.1 hj).2
    rw [abs_sub_comm] at this
    exact le_trans (by linarith) (le_max_left _ _)
  have hsub2 : ∑ j ∈ Finset.univ.filter (fun j : Fin n => |Real.log (p j) - x| ≤ θ),
        max (2 * θ - |x - Real.log (p j)|) 0 ≤ ∑ j, max (2 * θ - |x - Real.log (p j)|) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => le_max_right _ _)
  rw [Finset.sum_const, nsmul_eq_mul] at hsub
  linarith

lemma buffer_dist' (p : Fin n → ℝ) (hlip : LipschitzWith (1 / 2 : NNReal) (buffer p)) (x y : ℝ) :
    |buffer p x - buffer p y| ≤ 1 / 2 * |x - y| := by
  have h := hlip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at h
  have e : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [e] at h; exact h

lemma psi_strictMono (p : Fin n → ℝ) (hlip : LipschitzWith (1 / 2 : NNReal) (buffer p)) :
    StrictMono (fun x => x + buffer p x) := by
  intro x x' h
  have h1 := buffer_dist' p hlip x' x
  rw [abs_of_pos (sub_pos.2 h)] at h1
  have := (abs_le.1 h1).1
  show x + buffer p x < x' + buffer p x'
  linarith

lemma exists_b (p : Fin n → ℝ) (hlip : LipschitzWith (1 / 2 : NNReal) (buffer p))
    (hpos : ∀ x, 0 < buffer p x) (hle : ∀ x, buffer p x ≤ 1 / 2) (y : ℝ) :
    ∃ b, b + buffer p b = y := by
  have hcont : Continuous (fun x => x + buffer p x) := continuous_id.add hlip.continuous
  have h := intermediate_value_Icc (show y - 1 ≤ y by linarith) hcont.continuousOn
  have hy : y ∈ Icc ((fun x => x + buffer p x) (y - 1)) ((fun x => x + buffer p x) y) := by
    constructor
    · show y - 1 + buffer p (y - 1) ≤ y
      linarith [hle (y - 1)]
    · show y ≤ y + buffer p y
      linarith [hpos y]
  obtain ⟨b, _, hb⟩ := h hy
  exact ⟨b, hb⟩

end TranspositionIID.Main.Dev.L22
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L22
open TranspositionIID.Main TranspositionIID.Main.Dev.L21 MeasureTheory Set

variable {n : ℕ}

lemma f_sum (p : Fin n → ℝ) (σ : ListState n) (b : Fin n → ℝ)
    (hb : ∀ i, b i + buffer p (b i) = Real.log (p i))
    (hsm : StrictMono (fun x => x + buffer p x)) (x : ℝ) :
    Real.exp x * adaptiveInversions p x σ =
      ∑ i, ∑ j, (if σ j < σ i then (Ico (Real.log (p j)) (b i)).indicator Real.exp x else 0) := by
  unfold adaptiveInversions separatedInversions
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have hiff : x + buffer p x < Real.log (p i) ↔ x < b i := by
    have := hsm.lt_iff_lt (a := x) (b := b i)
    rw [hb i] at this
    exact this
  by_cases hs : σ j < σ i
  · by_cases h1 : Real.log (p j) ≤ x
    · by_cases h2 : x < b i
      · have h3 : x + buffer p x < Real.log (p i) := hiff.2 h2
        simp [hs, h1, h2, h3, Set.indicator, mem_Ico]
      · have h3 : ¬ (x + buffer p x < Real.log (p i)) := fun h => h2 (hiff.1 h)
        simp [hs, h1, h2, h3, Set.indicator, mem_Ico]
    · simp [hs, h1, Set.indicator, mem_Ico]
  · simp [hs]

lemma g_int (p : Fin n → ℝ) (σ : ListState n) (b : Fin n → ℝ) (i j : Fin n) :
    Integrable (fun x => if σ j < σ i then (Ico (Real.log (p j)) (b i)).indicator Real.exp x else 0) := by
  by_cases hs : σ j < σ i
  · simp only [hs, if_true]
    exact ((Real.continuous_exp.integrableOn_Icc).mono_set Ico_subset_Icc_self).integrable_indicator measurableSet_Ico
  · simp only [hs, if_false]
    exact integrable_zero _ _ _

lemma g_integral_nonneg (p : Fin n → ℝ) (σ : ListState n) (b : Fin n → ℝ) (i j : Fin n) :
    0 ≤ ∫ x in Iic 0, (if σ j < σ i then (Ico (Real.log (p j)) (b i)).indicator Real.exp x else 0) := by
  apply setIntegral_nonneg measurableSet_Iic
  intro x _
  split_ifs
  · exact Set.indicator_nonneg (fun y _ => (Real.exp_pos y).le) x
  · exact le_rfl

lemma g_integral (p : Fin n → ℝ) (σ : ListState n) (b : Fin n → ℝ) (i j : Fin n)
    (hb0 : b i ≤ 0) (hs : σ j < σ i) (hlt : Real.log (p j) < b i) :
    ∫ x in Iic 0, (if σ j < σ i then (Ico (Real.log (p j)) (b i)).indicator Real.exp x else 0) =
      Real.exp (b i) - Real.exp (Real.log (p j)) := by
  simp only [hs, if_true]
  rw [setIntegral_indicator measurableSet_Ico]
  have hsub : Iic (0 : ℝ) ∩ Ico (Real.log (p j)) (b i) = Ico (Real.log (p j)) (b i) := by
    apply Set.inter_eq_right.2
    intro x hx; exact le_trans hx.2.le hb0
  rw [hsub, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlt.le, integral_exp]

end TranspositionIID.Main.Dev.L22
end

section
set_option autoImplicit false

namespace TranspositionIID.Main
open TranspositionIID.Main.Dev.L21 TranspositionIID.Main.Dev.L22 MeasureTheory Set

theorem chk_lemma_2_2 {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i) (σ : ListState n) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp x * adaptiveInversions p x σ) (Set.Iic 0) ∧
    excess p σ ≤ 2 + (1 + Real.sqrt (Real.exp 1)) *
      (∫ x : ℝ in Set.Iic 0, Real.exp x * adaptiveInversions p x σ) := by
  have hl := lemma_2_1 hn p hp hsort hpos
  have hlip := hl.1
  have hθpos := buffer_pos hn p
  have hθle := buffer_le p
  choose b hb using fun i => exists_b p hlip hθpos hθle (Real.log (p i))
  have hsm := psi_strictMono p hlip
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp.2]; exact Finset.single_le_sum (f := p) (fun j _ => hp.1 j) (Finset.mem_univ i)
  have hy0 : ∀ i, Real.log (p i) ≤ 0 := fun i => Real.log_nonpos (hpos i).le (hp1 i)
  have hb0 : ∀ i, b i ≤ 0 := fun i => by linarith [hb i, hθpos (b i), hy0 i]
  set g : Fin n → Fin n → ℝ → ℝ := fun i j x =>
    if σ j < σ i then (Ico (Real.log (p j)) (b i)).indicator Real.exp x else 0 with hg
  have hfeq : (fun x : ℝ => Real.exp x * adaptiveInversions p x σ) = fun x => ∑ i, ∑ j, g i j x :=
    funext fun x => f_sum p σ b hb hsm x
  have hgint : ∀ i j, Integrable (g i j) := fun i j => g_int p σ b i j
  have hint : Integrable (fun x => ∑ i, ∑ j, g i j x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hgint i j
  rw [hfeq]
  refine ⟨hint.integrableOn, ?_⟩
  rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ => hgint i j).integrableOn]
  simp_rw [integral_finsetSum _ fun j _ => (hgint _ j).integrableOn]
  set s := Real.sqrt (Real.exp 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set cc : Fin n → Fin n → ℝ := fun i j => ∫ x in Iic 0, g i j x with hcc
  have hcc0 : ∀ i j, 0 ≤ cc i j := fun i j => g_integral_nonneg p σ b i j
  set aa : Fin n → Fin n → ℝ := fun i j =>
    if (p j < p i ∧ σ j < σ i) ∧ b i - buffer p (b i) ≤ Real.log (p j)
      then 2 * buffer p (b i) * p i else 0 with haa
  have haa0 : ∀ i j, 0 ≤ aa i j := fun i j => by
    simp only [haa]; split_ifs
    · have := hθpos (b i); have := hpos i; positivity
    · exact le_rfl
  have hpair : ∀ i j, (if p j < p i ∧ σ j < σ i then p i - p j else 0) ≤
      aa i j + (1 + s) * cc i j := by
    intro i j
    by_cases hP : p j < p i ∧ σ j < σ i
    · have hyj : Real.log (p j) < Real.log (p i) := Real.log_lt_log (hpos j) hP.1
      have hbi := hb i
      have hθb := hθpos (b i)
      have hθb2 := hθle (b i)
      by_cases hA : b i - buffer p (b i) ≤ Real.log (p j)
      · have h1 := A_scalar (Real.log (p i)) (Real.log (p j)) (buffer p (b i)) hyj.le
          (by linarith)
        rw [Real.exp_log (hpos i), Real.exp_log (hpos j)] at h1
        have : aa i j = 2 * buffer p (b i) * p i := by simp only [haa]; rw [if_pos ⟨hP, hA⟩]
        rw [if_pos hP, this]
        have := mul_nonneg (by linarith : 0 ≤ 1 + s) (hcc0 i j)
        linarith
      · push Not at hA
        have h1 := B_scalar (b i) (buffer p (b i)) (Real.log (p i)) (Real.log (p j)) hθb hθb2
          hbi.symm hA
        rw [Real.exp_log (hpos i), Real.exp_log (hpos j)] at h1
        have hc : cc i j = Real.exp (b i) - p j := by
          have := g_integral p σ b i j (hb0 i) hP.2 (by linarith)
          rw [Real.exp_log (hpos j)] at this
          exact this
        have : aa i j = 0 := by
          simp only [haa]; rw [if_neg (fun h => absurd h.2 (not_le.2 hA))]
        rw [if_pos hP, this, hc]
        linarith
    · rw [if_neg hP]
      have := haa0 i j
      have := mul_nonneg (by linarith : 0 ≤ 1 + s) (hcc0 i j)
      linarith
  have hsumA : ∑ i, ∑ j, aa i j ≤ 2 := by
    have hrow : ∀ i, ∑ j, aa i j ≤ 2 * p i := by
      intro i
      set θb := buffer p (b i) with hθb
      have hθbp : 0 < θb := hθpos _
      set Si := Finset.univ.filter (fun j : Fin n => |Real.log (p j) - b i| ≤ θb) with hSi
      have hle : ∀ j, aa i j ≤ if j ∈ Si then 2 * θb * p i else 0 := by
        intro j
        by_cases h : (p j < p i ∧ σ j < σ i) ∧ b i - θb ≤ Real.log (p j)
        · have hyj : Real.log (p j) < Real.log (p i) := Real.log_lt_log (hpos j) h.1.1
          have hmem : j ∈ Si := by
            rw [hSi, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [abs_le]; constructor <;> linarith [hb i, h.2]
          simp only [haa]; rw [if_pos h, if_pos hmem]
        · have : aa i j = 0 := by simp only [haa]; rw [if_neg h]
          rw [this]
          split_ifs
          · have := hpos i; positivity
          · exact le_rfl
      calc ∑ j, aa i j ≤ ∑ j, (if j ∈ Si then 2 * θb * p i else 0) :=
            Finset.sum_le_sum fun j _ => hle j
        _ = (Si.card : ℝ) * (2 * θb * p i) := by
            rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * p i := by
            have h1 := count_near hn p (b i)
            have := hpos i
            nlinarith
    calc ∑ i, ∑ j, aa i j ≤ ∑ i, 2 * p i := Finset.sum_le_sum fun i _ => hrow i
      _ = 2 := by rw [← Finset.mul_sum, hp.2]; ring
  have hexc : excess p σ = ∑ i, ∑ j, (if p j < p i ∧ σ j < σ i then p i - p j else 0) :=
    excess_eq_A p hsort σ
  rw [hexc]
  calc ∑ i, ∑ j, (if p j < p i ∧ σ j < σ i then p i - p j else 0)
      ≤ ∑ i, ∑ j, (aa i j + (1 + s) * cc i j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ∑ i, ∑ j, aa i j + (1 + s) * ∑ i, ∑ j, cc i j := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith

end TranspositionIID.Main
end

theorem solution : type_of% @TranspositionIID.Main.chk_lemma_2_2 := @TranspositionIID.Main.chk_lemma_2_2
