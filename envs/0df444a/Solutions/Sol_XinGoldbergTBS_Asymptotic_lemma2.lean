-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T14:59:09.254659+00:00
-- url     : https://prove2.me/submissions/a62b7973-496f-48c1-8650-1e510977f920

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace XGL2

open XinGoldbergTBS.Asymptotic

/-- right derivative of `G` -/
noncomputable def gd (κ : Costs) (y : ℝ) : ℝ := if 0 ≤ y then κ.h else -κ.b

lemma G_sub (κ : Costs) (w z : ℝ) : G κ w + gd κ w * (z - w) ≤ G κ z := by
  have hb := κ.b_pos; have hh := κ.h_pos
  unfold G gd
  by_cases hw : 0 ≤ w
  · rw [if_pos hw, max_eq_left hw, max_eq_right (by linarith : -w ≤ 0)]
    have h1 : z ≤ max z 0 := le_max_left _ _
    have h2 : 0 ≤ max (-z) 0 := le_max_right _ _
    nlinarith
  · rw [if_neg hw]
    push Not at hw
    rw [max_eq_right hw.le, max_eq_left (by linarith : (0:ℝ) ≤ -w)]
    have h1 : -z ≤ max (-z) 0 := le_max_left _ _
    have h2 : 0 ≤ max z 0 := le_max_right _ _
    nlinarith

lemma gd_mono (κ : Costs) : Monotone (gd κ) := by
  intro x y hxy
  have hb := κ.b_pos; have hh := κ.h_pos
  unfold gd
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (le_trans hx hxy)]
  · rw [if_neg hx]; split_ifs <;> linarith

lemma gd_abs (κ : Costs) (y : ℝ) : |gd κ y| ≤ max κ.b κ.h := by
  have hb := κ.b_pos; have hh := κ.h_pos
  unfold gd
  split_ifs
  · rw [abs_of_pos hh]; exact le_max_right _ _
  · rw [abs_neg, abs_of_pos hb]; exact le_max_left _ _

lemma measurable_gd (κ : Costs) : Measurable (gd κ) := by
  unfold gd
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

/-- truncation of a path to a finite index set -/
def trunc (S : Finset ℕ) (d : Path) : Path := fun j => if j ∈ S then d j else 0

lemma measurable_trunc (S : Finset ℕ) : Measurable (trunc S) := by
  apply measurable_pi_lambda
  intro j
  unfold trunc
  by_cases h : j ∈ S
  · simp only [h, if_true]; exact measurable_pi_apply j
  · simp only [h, if_false]; exact measurable_const

/-- base-stock trajectory: start `z0` at time 0, then order up to `s (k+1)` -/
def bs (r : ℝ) (s : ℕ → ℝ) (z0 : ℝ) (d : Path) : ℕ → ℝ
  | 0 => z0
  | k + 1 => max (bs r s z0 d k + r - d k) (s (k + 1))

/-- trajectory restarted at time `i` from level `z` -/
def bsF (r : ℝ) (s : ℕ → ℝ) (i : ℕ) (z : ℝ) (d : Path) : ℕ → ℝ
  | 0 => z
  | t + 1 => max (bsF r s i z d t + r - d (i + t)) (s (i + t + 1))

lemma bs_eq_bsF (r : ℝ) (s : ℕ → ℝ) (z0 : ℝ) (d : Path) (i t : ℕ) :
    bs r s z0 d (i + t) = bsF r s i (bs r s z0 d i) d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show bs r s z0 d (i + t + 1) = _
    simp only [bs, bsF, ih]

lemma bsF_mono (r : ℝ) (s : ℕ → ℝ) (i : ℕ) (d : Path) (t : ℕ) :
    Monotone (fun z => bsF r s i z d t) := by
  induction t with
  | zero => intro x y h; exact h
  | succ t ih =>
    intro x y h
    simp only [bsF]
    exact max_le_max (by linarith [ih h]) le_rfl

lemma bs_loc (r : ℝ) (s : ℕ → ℝ) (z0 : ℝ) (d d' : Path) (k : ℕ)
    (h : ∀ j < k, d j = d' j) : bs r s z0 d k = bs r s z0 d' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bs]
    rw [ih (fun j hj => h j (by omega)), h k (by omega)]

lemma bs_sloc (r : ℝ) (s s' : ℕ → ℝ) (z0 : ℝ) (d : Path) (k : ℕ)
    (h : ∀ j ≤ k, s j = s' j) : bs r s z0 d k = bs r s' z0 d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bs]
    rw [ih (fun j hj => h j (by omega)), h (k + 1) le_rfl]

lemma bsF_loc (r : ℝ) (s : ℕ → ℝ) (i : ℕ) (z : ℝ) (d d' : Path) (t : ℕ)
    (h : ∀ j < t, d (i + j) = d' (i + j)) : bsF r s i z d t = bsF r s i z d' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [bsF]
    rw [ih (fun j hj => h j (by omega)), h t (by omega)]

lemma measurable_bs (r : ℝ) (s : ℕ → ℝ) (z0 : ℝ) (k : ℕ) :
    Measurable (fun d : Path => bs r s z0 d k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [bs]
    exact ((ih.add measurable_const).sub (measurable_pi_apply k)).max measurable_const

lemma measurable_bsF (r : ℝ) (s : ℕ → ℝ) (i : ℕ) (z : ℝ) (t : ℕ) :
    Measurable (fun d : Path => bsF r s i z d t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [bsF]
    exact ((ih.add measurable_const).sub (measurable_pi_apply _)).max measurable_const

lemma bs_abs (r : ℝ) (s : ℕ → ℝ) (z0 : ℝ) (d : Path) (k : ℕ) :
    |bs r s z0 d k| ≤ |z0| + ∑ j ∈ Finset.range (k + 1), |s j| +
      ∑ j ∈ Finset.range k, (|r| + |d j|) := by
  induction k with
  | zero =>
    simp only [bs, zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty]
    linarith [abs_nonneg (s 0)]
  | succ k ih =>
    simp only [bs]
    rw [Finset.sum_range_succ (fun j => |s j|) (k + 1),
      Finset.sum_range_succ (fun j => |r| + |d j|) k]
    have h1 : |max (bs r s z0 d k + r - d k) (s (k + 1))| ≤
        |bs r s z0 d k + r - d k| + |s (k + 1)| := by
      rcases le_total (bs r s z0 d k + r - d k) (s (k + 1)) with h | h
      · rw [max_eq_right h]; linarith [abs_nonneg (bs r s z0 d k + r - d k)]
      · rw [max_eq_left h]; linarith [abs_nonneg (s (k + 1))]
    have h2 : |bs r s z0 d k + r - d k| ≤ |bs r s z0 d k| + |r| + |d k| := by
      calc |bs r s z0 d k + r - d k| ≤ |bs r s z0 d k + r| + |d k| := abs_sub _ _
        _ ≤ |bs r s z0 d k| + |r| + |d k| := by linarith [abs_add_le (bs r s z0 d k) r]
    linarith

/-- finite sum swap -/
lemma sum_swap (A x : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, A k * ∑ i ∈ Finset.range (k + 1), x i =
      ∑ i ∈ Finset.range n, x i * ∑ j ∈ Finset.Ico i n, A j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : ∀ i ∈ Finset.range (n + 1), x i * ∑ j ∈ Finset.Ico i (n + 1), A j =
        x i * ∑ j ∈ Finset.Ico i n, A j + x i * A n := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.sum_Ico_succ_top (by omega), mul_add]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_range_succ (fun i =>
      x i * ∑ j ∈ Finset.Ico i n, A j), Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero,
      ← Finset.sum_mul]
    ring

end XGL2

namespace XGL2

open XinGoldbergTBS.Asymptotic

/-- demand path of the witness -/
def Dv {Ω : Type*} (D : ℕ → Ω → ℝ) (ω : Ω) : Path := fun j => D j ω

def Sw (L₀ : ℕ) (d : Path) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (L₀ + 1), d (k + j)

def wF (L₀ : ℕ) (a r : ℝ) (F : ℕ → Path → ℝ) (d : Path) (k : ℕ) : ℝ :=
  a + ∑ i ∈ Finset.range k, (r - d i) + ∑ i ∈ Finset.range (k + 1), F i d - Sw L₀ d k

noncomputable def gsum (κ : Costs) (L₀ : ℕ) (α a r : ℝ) (F : ℕ → Path → ℝ) (n i : ℕ)
    (d : Path) : ℝ :=
  ∑ j ∈ Finset.Ico i n, α ^ j * gd κ (wF L₀ a r F d j)

def Yk {Ω : Type*} (L₀ L : ℕ) (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ)
    (I : Ω → ℝ) (D : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  I ω + ∑ i ∈ Finset.range k, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω) + qN L₀ L q ω k
    - ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω

lemma measurable_Dv {Ω : Type*} [MeasurableSpace Ω] (D : ℕ → Ω → ℝ)
    (hD : ∀ j, Measurable (D j)) : Measurable (Dv D) :=
  measurable_pi_lambda _ hD

lemma measurable_Sw (L₀ k : ℕ) : Measurable (fun d : Path => Sw L₀ d k) := by
  unfold Sw
  exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply _)

lemma measurable_wF (L₀ : ℕ) (a r : ℝ) (F : ℕ → Path → ℝ) (hF : ∀ i, Measurable (F i))
    (k : ℕ) : Measurable (fun d : Path => wF L₀ a r F d k) := by
  unfold wF
  refine ((measurable_const.add ?_).add ?_).sub (measurable_Sw L₀ k)
  · exact Finset.measurable_sum _ (fun i _ => measurable_const.sub (measurable_pi_apply i))
  · exact Finset.measurable_sum _ (fun i _ => hF i)

lemma measurable_gsum (κ : Costs) (L₀ : ℕ) (α a r : ℝ) (F : ℕ → Path → ℝ)
    (hF : ∀ i, Measurable (F i)) (n i : ℕ) : Measurable (gsum κ L₀ α a r F n i) := by
  unfold gsum
  exact Finset.measurable_sum _ (fun j _ =>
    measurable_const.mul ((measurable_gd κ).comp (measurable_wF L₀ a r F hF j)))

lemma gsum_abs (κ : Costs) (L₀ : ℕ) (α a r : ℝ) (hα : 0 ≤ α) (F : ℕ → Path → ℝ) (n i : ℕ)
    (d : Path) : |gsum κ L₀ α a r F n i d| ≤
      ∑ j ∈ Finset.range n, α ^ j * max κ.b κ.h := by
  unfold gsum
  calc |∑ j ∈ Finset.Ico i n, α ^ j * gd κ (wF L₀ a r F d j)|
      ≤ ∑ j ∈ Finset.Ico i n, |α ^ j * gd κ (wF L₀ a r F d j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ico i n, α ^ j * max κ.b κ.h := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_of_nonneg (pow_nonneg hα j)]
        exact mul_le_mul_of_nonneg_left (gd_abs κ _) (pow_nonneg hα j)
    _ ≤ ∑ j ∈ Finset.range n, α ^ j * max κ.b κ.h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj; simp only [Finset.mem_Ico] at hj; simp only [Finset.mem_range]; omega
        · intro j _ _
          exact mul_nonneg (pow_nonneg hα j) (le_trans κ.b_pos.le (le_max_left _ _))

lemma Y_sub_w {Ω : Type*} (L₀ L : ℕ) (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ)
    (I : Ω → ℝ) (D : ℕ → Ω → ℝ) (a r : ℝ) (F : ℕ → Path → ℝ) (k : ℕ) (ω : Ω) :
    Yk L₀ L χ q I D k ω - wF L₀ a r F (Dv D ω) k =
      (I ω - a) + ∑ i ∈ Finset.range k, (chiN L₀ L χ ω i - r) +
        ∑ i ∈ Finset.range (k + 1), (qN L₀ L q ω i - F i (Dv D ω)) := by
  unfold Yk wF Sw Dv
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_range_succ,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- extension of a finset-indexed vector by zero -/
def ext (S : Finset ℕ) (v : S → ℝ) : Path := fun j => if h : j ∈ S then v ⟨j, h⟩ else 0

lemma measurable_ext (S : Finset ℕ) : Measurable (ext S) := by
  apply measurable_pi_lambda
  intro j
  unfold ext
  by_cases h : j ∈ S
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma ext_restrict (S : Finset ℕ) (d : Path) : ext S (fun j : S => d j) = trunc S d := by
  funext j
  unfold ext trunc
  by_cases h : j ∈ S <;> simp [h]

/-- independence of functions of disjoint finite blocks of the demands -/
lemma indep_blocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : ℕ → Ω → ℝ)
    (hD : ∀ j, Measurable (D j)) (hind : iIndepFun D P) (S T : Finset ℕ) (hST : Disjoint S T)
    (Φ Ψ : Path → ℝ) (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    IndepFun (fun ω => Φ (trunc S (Dv D ω))) (fun ω => Ψ (trunc T (Dv D ω))) P := by
  have h := (hind.indepFun_finset S T hST hD).comp (hΦ.comp (measurable_ext S))
    (hΨ.comp (measurable_ext T))
  have e1 : (fun ω => Φ (trunc S (Dv D ω))) = (Φ ∘ ext S) ∘ (fun ω (j : S) => D j ω) := by
    funext ω; simp only [Function.comp]; rw [← ext_restrict]; rfl
  have e2 : (fun ω => Ψ (trunc T (Dv D ω))) = (Ψ ∘ ext T) ∘ (fun ω (j : T) => D j ω) := by
    funext ω; simp only [Function.comp]; rw [← ext_restrict]; rfl
  rw [e1, e2]; exact h

/-- shift-back of a tail path -/
def unshift (i : ℕ) (e : Path) : Path := fun j => if i ≤ j then e (j - i) else 0

lemma measurable_unshift (i : ℕ) : Measurable (unshift i) := by
  apply measurable_pi_lambda
  intro j
  unfold unshift
  by_cases h : i ≤ j
  · simp only [h, if_true]; exact measurable_pi_apply _
  · simp only [h, if_false]; exact measurable_const

lemma trunc_unshift (i N : ℕ) (d : Path) :
    trunc (Finset.Ico i N) (unshift i (fun j => d (i + j))) = trunc (Finset.Ico i N) d := by
  funext j
  unfold trunc unshift
  by_cases h : j ∈ Finset.Ico i N
  · have hij : i ≤ j := (Finset.mem_Ico.mp h).1
    simp only [h, if_true, hij]
    congr 1; omega
  · simp [h]

end XGL2

namespace XGL2

open XinGoldbergTBS.Asymptotic

def Wt {Ω : Type*} (L₀ : ℕ) (a r : ℝ) (F : ℕ → Path → ℝ) (D : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  wF L₀ a r F (Dv D ω) k

def Xq {Ω : Type*} (L₀ L : ℕ) (q : Ω → Fin (L - L₀) → ℝ) (F : ℕ → Path → ℝ)
    (D : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  qN L₀ L q ω i - F i (Dv D ω)

section core

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : DemandLaw} {κ : Costs}
  {L₀ L : ℕ} {χ : Ω → Fin (L - L₀ - 1) → ℝ} {q : Ω → Fin (L - L₀) → ℝ} {I : Ω → ℝ}
  {D : ℕ → Ω → ℝ}

lemma integrable_D (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (j : ℕ) :
    Integrable (D j) P := by
  have h : Integrable id (P.map (D j)) := by rw [hw.law_D j]; exact μ.integrable
  exact h.comp_measurable (hw.measurable_D j)

lemma integrable_qN (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (i : ℕ) :
    Integrable (fun ω => qN L₀ L q ω i) P := by
  haveI := hw.isProb
  unfold qN
  by_cases h : i < L - L₀
  · simp only [dif_pos h]; exact hw.integrable_q ⟨i, h⟩
  · simp only [dif_neg h]; exact integrable_const 0

lemma integrable_chiN (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (i : ℕ) :
    Integrable (fun ω => chiN L₀ L χ ω i) P := by
  haveI := hw.isProb
  unfold chiN
  by_cases h : i < L - L₀ - 1
  · simp only [dif_pos h]; exact hw.integrable_chi ⟨i, h⟩
  · simp only [dif_neg h]; exact integrable_const 0

lemma integrable_G (κ : Costs) {f : Ω → ℝ} (hf : Integrable f P) :
    Integrable (fun ω => G κ (f ω)) P := by
  unfold G
  exact (hf.pos_part.const_mul κ.h).add (hf.neg.pos_part.const_mul κ.b)

lemma integrable_Yk (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (k : ℕ) :
    Integrable (Yk L₀ L χ q I D k) P := by
  unfold Yk
  have h1 : Integrable (fun ω => ∑ i ∈ Finset.range k,
      (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)) P :=
    integrable_finsetSum _ (fun i _ =>
      ((integrable_qN hw i).add (integrable_chiN hw i)).sub (integrable_D hw i))
  have h2 : Integrable (fun ω => ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω) P :=
    integrable_finsetSum _ (fun i _ => integrable_D hw (k + i))
  exact ((hw.integrable_I.add h1).add (integrable_qN hw k)).sub h2

lemma integrable_Wt (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (a r : ℝ)
    (F : ℕ → Path → ℝ) (hFint : ∀ i, Integrable (fun ω => F i (Dv D ω)) P) (k : ℕ) :
    Integrable (Wt L₀ a r F D k) P := by
  haveI := hw.isProb
  unfold Wt wF Sw
  have h1 : Integrable (fun ω => ∑ i ∈ Finset.range k, (r - Dv D ω i)) P :=
    integrable_finsetSum _ (fun i _ => (integrable_const r).sub (integrable_D hw i))
  have h2 : Integrable (fun ω => ∑ i ∈ Finset.range (k + 1), F i (Dv D ω)) P :=
    integrable_finsetSum _ (fun i _ => hFint i)
  have h3 : Integrable (fun ω => ∑ j ∈ Finset.range (L₀ + 1), Dv D ω (k + j)) P :=
    integrable_finsetSum _ (fun j _ => integrable_D hw (k + j))
  exact (((integrable_const a).add h1).add h2).sub h3

lemma measurable_Wt (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (a r : ℝ)
    (F : ℕ → Path → ℝ) (hFm : ∀ i, Measurable (F i)) (k : ℕ) :
    Measurable (Wt L₀ a r F D k) :=
  (measurable_wF L₀ a r F hFm k).comp (measurable_Dv D hw.measurable_D)

lemma chiN_mean (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (hL : L₀ + 1 < L) (i : ℕ)
    (hi : i < L - L₀ - 1) : ∫ ω, chiN L₀ L χ ω i ∂P = rL P L₀ L χ := by
  have h0 : 0 < L - L₀ - 1 := by omega
  unfold rL chiN
  simp only [dif_pos hi, dif_pos h0]
  exact (hw.ident_chi ⟨i, hi⟩ ⟨0, h0⟩).integral_eq

lemma qN_mean (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (hL : L₀ + 1 < L) (i : ℕ)
    (hi : i < L - L₀) : ∫ ω, qN L₀ L q ω i ∂P = ∫ ω, qN L₀ L q ω 0 ∂P := by
  have h0 : 0 < L - L₀ := by omega
  unfold qN
  simp only [dif_pos hi, dif_pos h0]
  exact (hw.ident_q ⟨i, hi⟩ ⟨0, h0⟩).integral_eq

theorem core (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (hL : L₀ + 1 < L)
    (n : ℕ) (hn : L - L₀ = n) (a r : ℝ) (ha : ∫ ω, I ω ∂P = a) (hr : rL P L₀ L χ = r)
    (α : ℝ) (hα : 0 ≤ α)
    (F Lam : ℕ → Path → ℝ) (C : ℝ)
    (hFm : ∀ i, Measurable (F i)) (hF0 : ∀ i d, 0 ≤ F i d)
    (hFloc : ∀ i d, F i d = F i (trunc (Finset.range i) d))
    (hFint : ∀ i, Integrable (fun ω => F i (Dv D ω)) P)
    (hFmean : ∀ i, i < n → ∫ ω, F i (Dv D ω) ∂P = ∫ ω, qN L₀ L q ω 0 ∂P)
    (hLm : ∀ i, Measurable (Lam i)) (hLb : ∀ i d, |Lam i d| ≤ C)
    (hLloc : ∀ i d, Lam i d = Lam i (trunc (Finset.Ico i (n + L₀)) d))
    (hge : ∀ i, i < n → ∀ d, Lam i d ≤ gsum κ L₀ α a r F n i d)
    (heq : ∀ i, i < n → ∀ d, F i d * gsum κ L₀ α a r F n i d = F i d * Lam i d) :
    ∑ k ∈ Finset.range n, α ^ k * ∫ ω, G κ (Wt L₀ a r F D k ω) ∂P ≤
      ∑ k ∈ Finset.range n, α ^ k * ∫ ω, G κ (Yk L₀ L χ q I D k ω) ∂P := by
  haveI := hw.isProb
  have hgdm : ∀ k, AEStronglyMeasurable (fun ω => gd κ (Wt L₀ a r F D k ω)) P := fun k =>
    ((measurable_gd κ).comp (measurable_Wt hw a r F hFm k)).aestronglyMeasurable
  have hgdb : ∀ k, ∀ᵐ ω ∂P, ‖gd κ (Wt L₀ a r F D k ω)‖ ≤ max κ.b κ.h := fun k =>
    ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact gd_abs κ _)
  have hX : ∀ i, Integrable (Xq L₀ L q F D i) P := fun i =>
    (integrable_qN hw i).sub (hFint i)
  -- per-period subgradient bound
  have hkb : ∀ k, k < n → ∫ ω, G κ (Wt L₀ a r F D k ω) ∂P +
      ∫ ω, gd κ (Wt L₀ a r F D k ω) * ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ∂P ≤
      ∫ ω, G κ (Yk L₀ L χ q I D k ω) ∂P := by
    intro k hkn
    have hE1 : Integrable (fun ω => gd κ (Wt L₀ a r F D k ω) * (I ω - a)) P :=
      (hw.integrable_I.sub (integrable_const a)).bdd_mul (hgdm k) (hgdb k)
    have hE2i : ∀ i, Integrable (fun ω => gd κ (Wt L₀ a r F D k ω) *
        (chiN L₀ L χ ω i - r)) P := fun i =>
      ((integrable_chiN hw i).sub (integrable_const r)).bdd_mul (hgdm k) (hgdb k)
    have hE2 : Integrable (fun ω => ∑ i ∈ Finset.range k, gd κ (Wt L₀ a r F D k ω) *
        (chiN L₀ L χ ω i - r)) P := integrable_finsetSum _ (fun i _ => hE2i i)
    have hE3 : Integrable (fun ω => gd κ (Wt L₀ a r F D k ω) *
        ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω) P :=
      (integrable_finsetSum _ (fun i _ => hX i)).bdd_mul (hgdm k) (hgdb k)
    have hGW : Integrable (fun ω => G κ (Wt L₀ a r F D k ω)) P :=
      integrable_G κ (integrable_Wt hw a r F hFint k)
    have hA : Integrable (fun ω => G κ (Wt L₀ a r F D k ω) +
        gd κ (Wt L₀ a r F D k ω) * (I ω - a)) P := hGW.add hE1
    have hB : Integrable (fun ω => G κ (Wt L₀ a r F D k ω) +
        gd κ (Wt L₀ a r F D k ω) * (I ω - a) + ∑ i ∈ Finset.range k,
          gd κ (Wt L₀ a r F D k ω) * (chiN L₀ L χ ω i - r)) P := hA.add hE2
    have hC : Integrable (fun ω => G κ (Wt L₀ a r F D k ω) +
        gd κ (Wt L₀ a r F D k ω) * (I ω - a) + ∑ i ∈ Finset.range k,
          gd κ (Wt L₀ a r F D k ω) * (chiN L₀ L χ ω i - r) +
        gd κ (Wt L₀ a r F D k ω) * ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω) P :=
      hB.add hE3
    have hpt : ∀ ω, G κ (Wt L₀ a r F D k ω) + gd κ (Wt L₀ a r F D k ω) * (I ω - a) +
        ∑ i ∈ Finset.range k, gd κ (Wt L₀ a r F D k ω) * (chiN L₀ L χ ω i - r) +
        gd κ (Wt L₀ a r F D k ω) * ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ≤
        G κ (Yk L₀ L χ q I D k ω) := by
      intro ω
      have h1 := G_sub κ (Wt L₀ a r F D k ω) (Yk L₀ L χ q I D k ω)
      have h2 := Y_sub_w L₀ L χ q I D a r F k ω
      have h3 : gd κ (Wt L₀ a r F D k ω) * (Yk L₀ L χ q I D k ω - Wt L₀ a r F D k ω) =
          gd κ (Wt L₀ a r F D k ω) * (I ω - a) +
          ∑ i ∈ Finset.range k, gd κ (Wt L₀ a r F D k ω) * (chiN L₀ L χ ω i - r) +
          gd κ (Wt L₀ a r F D k ω) * ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω := by
        unfold Wt Xq
        rw [h2, mul_add, mul_add, Finset.mul_sum]
      linarith
    have hint := integral_mono hC (integrable_G κ (integrable_Yk hw k)) hpt
    rw [integral_add hB hE3, integral_add hA hE2, integral_add hGW hE1,
      integral_finsetSum _ (fun i _ => hE2i i)] at hint
    have hI0 : ∫ ω, gd κ (Wt L₀ a r F D k ω) * (I ω - a) ∂P = 0 := by
      have hind : IndepFun (fun ω => gd κ (Wt L₀ a r F D k ω)) (fun ω => I ω - a) P :=
        hw.indep_chi_I.symm.comp (φ := fun d : Path => gd κ (wF L₀ a r F d k))
          (ψ := fun p : (Fin (L - L₀ - 1) → ℝ) × ℝ => p.2 - a)
          ((measurable_gd κ).comp (measurable_wF L₀ a r F hFm k))
          (measurable_snd.sub measurable_const)
      rw [hind.integral_fun_mul_eq_mul_integral (hgdm k)
        (hw.integrable_I.sub (integrable_const a)).aestronglyMeasurable]
      have h0 : ∫ ω, (I ω - a) ∂P = 0 := by
        rw [integral_sub hw.integrable_I (integrable_const a), ha]; simp
      simp only [h0, mul_zero]
    have hC0 : ∀ i ∈ Finset.range k,
        ∫ ω, gd κ (Wt L₀ a r F D k ω) * (chiN L₀ L χ ω i - r) ∂P = 0 := by
      intro i hi
      have hi' : i < L - L₀ - 1 := by simp only [Finset.mem_range] at hi; omega
      have e : (fun ω => chiN L₀ L χ ω i - r) = fun ω => χ ω ⟨i, hi'⟩ - r := by
        funext ω; simp only [chiN, dif_pos hi']
      have hind : IndepFun (fun ω => gd κ (Wt L₀ a r F D k ω))
          (fun ω => chiN L₀ L χ ω i - r) P := by
        rw [e]
        exact hw.indep_chi_I.symm.comp (φ := fun d : Path => gd κ (wF L₀ a r F d k))
          (ψ := fun p : (Fin (L - L₀ - 1) → ℝ) × ℝ => p.1 ⟨i, hi'⟩ - r)
          ((measurable_gd κ).comp (measurable_wF L₀ a r F hFm k))
          (((measurable_pi_apply _).comp measurable_fst).sub measurable_const)
      rw [hind.integral_fun_mul_eq_mul_integral (hgdm k)
        ((integrable_chiN hw i).sub (integrable_const r)).aestronglyMeasurable]
      have h0 : ∫ ω, (chiN L₀ L χ ω i - r) ∂P = 0 := by
        rw [integral_sub (integrable_chiN hw i) (integrable_const r), chiN_mean hw hL i hi', hr]
        simp
      simp only [h0, mul_zero]
    rw [hI0, Finset.sum_eq_zero hC0] at hint
    linarith
  -- the order terms
  have hq : ∀ i, i < n → 0 ≤ ∫ ω, gsum κ L₀ α a r F n i (Dv D ω) * Xq L₀ L q F D i ω ∂P := by
    intro i hi
    have hin : i < L - L₀ := by omega
    have hΛm : Measurable (fun ω => Lam i (Dv D ω)) :=
      (hLm i).comp (measurable_Dv D hw.measurable_D)
    have hΛb : ∀ᵐ ω ∂P, ‖Lam i (Dv D ω)‖ ≤ C :=
      ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hLb i _)
    have hgsm : Measurable (fun ω => gsum κ L₀ α a r F n i (Dv D ω)) :=
      (measurable_gsum κ L₀ α a r F hFm n i).comp (measurable_Dv D hw.measurable_D)
    have hgsb : ∀ᵐ ω ∂P, ‖gsum κ L₀ α a r F n i (Dv D ω)‖ ≤
        ∑ j ∈ Finset.range n, α ^ j * max κ.b κ.h :=
      ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact gsum_abs κ L₀ α a r hα F n i _)
    have hI1 : Integrable (fun ω => Lam i (Dv D ω) * qN L₀ L q ω i) P :=
      (integrable_qN hw i).bdd_mul hΛm.aestronglyMeasurable hΛb
    have hI2 : Integrable (fun ω => Lam i (Dv D ω) * F i (Dv D ω)) P :=
      (hFint i).bdd_mul hΛm.aestronglyMeasurable hΛb
    have hlo : Integrable (fun ω => Lam i (Dv D ω) * qN L₀ L q ω i -
        Lam i (Dv D ω) * F i (Dv D ω)) P := hI1.sub hI2
    have hhi : Integrable (fun ω => gsum κ L₀ α a r F n i (Dv D ω) * Xq L₀ L q F D i ω) P :=
      (hX i).bdd_mul hgsm.aestronglyMeasurable hgsb
    have hpt : ∀ᵐ ω ∂P, Lam i (Dv D ω) * qN L₀ L q ω i - Lam i (Dv D ω) * F i (Dv D ω) ≤
        gsum κ L₀ α a r F n i (Dv D ω) * Xq L₀ L q F D i ω := by
      filter_upwards [hw.nonneg] with ω hω
      have hq0 : 0 ≤ qN L₀ L q ω i := by
        unfold qN; rw [dif_pos hin]; exact hω.2 _
      have h1 := hge i hi (Dv D ω)
      have h2 := heq i hi (Dv D ω)
      have h3 : Lam i (Dv D ω) * qN L₀ L q ω i ≤
          gsum κ L₀ α a r F n i (Dv D ω) * qN L₀ L q ω i :=
        mul_le_mul_of_nonneg_right h1 hq0
      unfold Xq
      rw [mul_sub]
      linarith
    have hmono := integral_mono_ae hlo hhi hpt
    -- independence: Λ_i ⊥ q_i and Λ_i ⊥ F_i
    set Ψ : Path → ℝ := fun e => Lam i (trunc (Finset.Ico i (n + L₀)) (unshift i e)) with hΨ
    have hΨm : Measurable Ψ :=
      (hLm i).comp ((measurable_trunc _).comp (measurable_unshift i))
    have hΛΨ : (fun ω => Lam i (Dv D ω)) = Ψ ∘ (fun ω j => D (i + j) ω) := by
      funext ω
      simp only [Function.comp, hΨ]
      rw [hLloc i (Dv D ω)]
      have := trunc_unshift i (n + L₀) (Dv D ω)
      unfold Dv at this ⊢
      rw [this]
    have hind1 : IndepFun (fun ω => Lam i (Dv D ω)) (fun ω => qN L₀ L q ω i) P := by
      have e : (fun ω => qN L₀ L q ω i) = fun ω => q ω ⟨i, hin⟩ := by
        funext ω; simp only [qN, dif_pos hin]
      rw [hΛΨ, e]
      exact (hw.indep_q ⟨i, hin⟩).symm.comp hΨm measurable_id
    have hind2 : IndepFun (fun ω => Lam i (Dv D ω)) (fun ω => F i (Dv D ω)) P := by
      have hdis : Disjoint (Finset.Ico i (n + L₀)) (Finset.range i) := by
        rw [Finset.disjoint_left]
        intro j hj hj'
        simp only [Finset.mem_Ico] at hj
        simp only [Finset.mem_range] at hj'
        omega
      have h := indep_blocks D hw.measurable_D hw.indep_D _ _ hdis (Lam i) (F i) (hLm i) (hFm i)
      have e1 : (fun ω => Lam i (Dv D ω)) =
          fun ω => Lam i (trunc (Finset.Ico i (n + L₀)) (Dv D ω)) := by
        funext ω; exact hLloc i _
      have e2 : (fun ω => F i (Dv D ω)) = fun ω => F i (trunc (Finset.range i) (Dv D ω)) := by
        funext ω; exact hFloc i _
      rw [e1, e2]; exact h
    have hz : ∫ ω, (Lam i (Dv D ω) * qN L₀ L q ω i - Lam i (Dv D ω) * F i (Dv D ω)) ∂P = 0 := by
      rw [integral_sub hI1 hI2,
        hind1.integral_fun_mul_eq_mul_integral hΛm.aestronglyMeasurable
          (integrable_qN hw i).aestronglyMeasurable,
        hind2.integral_fun_mul_eq_mul_integral hΛm.aestronglyMeasurable
          (hFint i).aestronglyMeasurable]
      have e3 : ∫ ω, qN L₀ L q ω i ∂P = ∫ ω, qN L₀ L q ω 0 ∂P := qN_mean hw hL i hin
      have e4 : ∫ ω, F i (Dv D ω) ∂P = ∫ ω, qN L₀ L q ω 0 ∂P := hFmean i hi
      simp only [e3, e4, sub_self]
    linarith
  -- sum swap and assembly
  have hsum : ∑ k ∈ Finset.range n, α ^ k * ∫ ω, gd κ (Wt L₀ a r F D k ω) *
        ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ∂P =
      ∑ i ∈ Finset.range n, ∫ ω, gsum κ L₀ α a r F n i (Dv D ω) * Xq L₀ L q F D i ω ∂P := by
    have hE3 : ∀ k, Integrable (fun ω => α ^ k * (gd κ (Wt L₀ a r F D k ω) *
        ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω)) P := fun k =>
      ((integrable_finsetSum _ (fun i _ => hX i)).bdd_mul (hgdm k) (hgdb k)).const_mul _
    have hG : ∀ i, Integrable (fun ω => gsum κ L₀ α a r F n i (Dv D ω) * Xq L₀ L q F D i ω) P :=
      fun i => (hX i).bdd_mul
        ((measurable_gsum κ L₀ α a r F hFm n i).comp
          (measurable_Dv D hw.measurable_D)).aestronglyMeasurable
        (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact gsum_abs κ L₀ α a r hα F n i _))
    have e1 : ∀ k ∈ Finset.range n, α ^ k * ∫ ω, gd κ (Wt L₀ a r F D k ω) *
        ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ∂P =
        ∫ ω, α ^ k * (gd κ (Wt L₀ a r F D k ω) *
          ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω) ∂P := by
      intro k _; rw [integral_const_mul]
    rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ (fun k _ => hE3 k),
      ← integral_finsetSum _ (fun i _ => hG i)]
    congr 1; funext ω
    have hs := sum_swap (fun k => α ^ k * gd κ (Wt L₀ a r F D k ω))
      (fun i => Xq L₀ L q F D i ω) n
    have e2 : ∀ k ∈ Finset.range n, α ^ k * (gd κ (Wt L₀ a r F D k ω) *
        ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω) =
        α ^ k * gd κ (Wt L₀ a r F D k ω) * ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω := by
      intro k _; ring
    rw [Finset.sum_congr rfl e2, hs]
    apply Finset.sum_congr rfl
    intro i _
    unfold gsum
    rw [mul_comm]
    rfl
  have hpos : 0 ≤ ∑ k ∈ Finset.range n, α ^ k * ∫ ω, gd κ (Wt L₀ a r F D k ω) *
        ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ∂P := by
    rw [hsum]
    exact Finset.sum_nonneg (fun i hi => hq i (Finset.mem_range.mp hi))
  calc ∑ k ∈ Finset.range n, α ^ k * ∫ ω, G κ (Wt L₀ a r F D k ω) ∂P
      ≤ ∑ k ∈ Finset.range n, α ^ k * ∫ ω, G κ (Wt L₀ a r F D k ω) ∂P +
        ∑ k ∈ Finset.range n, α ^ k * ∫ ω, gd κ (Wt L₀ a r F D k ω) *
          ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ∂P := le_add_of_nonneg_right hpos
    _ = ∑ k ∈ Finset.range n, α ^ k * (∫ ω, G κ (Wt L₀ a r F D k ω) ∂P +
        ∫ ω, gd κ (Wt L₀ a r F D k ω) *
          ∑ i ∈ Finset.range (k + 1), Xq L₀ L q F D i ω ∂P) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ ∑ k ∈ Finset.range n, α ^ k * ∫ ω, G κ (Yk L₀ L χ q I D k ω) ∂P :=
        Finset.sum_le_sum (fun k hk' => mul_le_mul_of_nonneg_left
          (hkb k (Finset.mem_range.mp hk')) (pow_nonneg hα k))

end core

end XGL2

namespace XGL2

open XinGoldbergTBS.Asymptotic

/-! ## The base-stock comparison policy -/

def sig (a ε : ℝ) (s : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then a + ε else s i

def Fb (r a ε : ℝ) (s : ℕ → ℝ) : ℕ → Path → ℝ
  | 0, _ => ε
  | i + 1, d => bs r s (a + ε) d (i + 1) - (bs r s (a + ε) d i + r - d i)

noncomputable def LamB (κ : Costs) (L₀ n : ℕ) (α r a ε : ℝ) (s : ℕ → ℝ) (i : ℕ) (d : Path) : ℝ :=
  ∑ j ∈ Finset.Ico i n, α ^ j * gd κ (bsF r s i (sig a ε s i) d (j - i) - Sw L₀ d j)

section bsc

variable (κ : Costs) (L₀ n : ℕ) (α r a ε : ℝ) (s : ℕ → ℝ)

lemma wF_Fb (d : Path) (k : ℕ) :
    wF L₀ a r (Fb r a ε s) d k = bs r s (a + ε) d k - Sw L₀ d k := by
  have key : ∀ k, a + ∑ i ∈ Finset.range k, (r - d i) +
      ∑ i ∈ Finset.range (k + 1), Fb r a ε s i d = bs r s (a + ε) d k := by
    intro k
    induction k with
    | zero => simp [Fb, bs]
    | succ k ih =>
      rw [Finset.sum_range_succ (fun i => r - d i) k,
        Finset.sum_range_succ (fun i => Fb r a ε s i d) (k + 1)]
      have hF : Fb r a ε s (k + 1) d =
          bs r s (a + ε) d (k + 1) - (bs r s (a + ε) d k + r - d k) := rfl
      rw [hF]
      linarith
  unfold wF
  rw [key k]

lemma Fb_nonneg (hε : 0 ≤ ε) (i : ℕ) (d : Path) : 0 ≤ Fb r a ε s i d := by
  cases i with
  | zero => exact hε
  | succ i =>
    simp only [Fb, bs]
    linarith [le_max_left (bs r s (a + ε) d i + r - d i) (s (i + 1))]

lemma Fb_loc (i : ℕ) (d : Path) : Fb r a ε s i d = Fb r a ε s i (trunc (Finset.range i) d) := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [Fb]
    have h1 : ∀ j < i + 1, d j = trunc (Finset.range (i + 1)) d j := by
      intro j hj; unfold trunc; rw [if_pos (Finset.mem_range.mpr hj)]
    rw [bs_loc r s _ d _ (i + 1) h1, bs_loc r s _ d _ i (fun j hj => h1 j (by omega)),
      h1 i (by omega)]

lemma measurable_Fb (i : ℕ) : Measurable (Fb r a ε s i) := by
  cases i with
  | zero => exact measurable_const
  | succ i =>
    exact (measurable_bs r s _ (i + 1)).sub
      (((measurable_bs r s _ i).add measurable_const).sub (measurable_pi_apply i))

lemma Fb_sloc (s' : ℕ → ℝ) (i : ℕ) (h : ∀ j ≤ i, s j = s' j) (d : Path) :
    Fb r a ε s i d = Fb r a ε s' i d := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [Fb]
    rw [bs_sloc r s s' _ d (i + 1) h, bs_sloc r s s' _ d i (fun j hj => h j (by omega))]

lemma bs_ge_sig (i : ℕ) (d : Path) : sig a ε s i ≤ bs r s (a + ε) d i := by
  cases i with
  | zero => simp [sig, bs]
  | succ i => simp only [sig, bs]; simp

lemma bs_eq_or (i : ℕ) (d : Path) : bs r s (a + ε) d i = sig a ε s i ∨ Fb r a ε s i d = 0 := by
  cases i with
  | zero => left; simp [sig, bs]
  | succ i =>
    rcases le_total (bs r s (a + ε) d i + r - d i) (s (i + 1)) with h | h
    · left; simp only [sig, bs]; simp [max_eq_right h]
    · right; simp only [Fb, bs]; rw [max_eq_left h]; ring

lemma bs_shift (i j : ℕ) (hij : i ≤ j) (d : Path) :
    bs r s (a + ε) d j = bsF r s i (bs r s (a + ε) d i) d (j - i) := by
  have := bs_eq_bsF r s (a + ε) d i (j - i)
  rwa [Nat.add_sub_cancel' hij] at this

lemma LamB_le (hα : 0 ≤ α) (i : ℕ) (d : Path) :
    LamB κ L₀ n α r a ε s i d ≤ gsum κ L₀ α a r (Fb r a ε s) n i d := by
  unfold LamB gsum
  apply Finset.sum_le_sum
  intro j hj
  have hij : i ≤ j := (Finset.mem_Ico.mp hj).1
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα j)
  apply gd_mono
  rw [wF_Fb, bs_shift r a ε s i j hij d]
  have := bsF_mono r s i d (j - i) (bs_ge_sig r a ε s i d)
  simp only at this
  linarith

lemma LamB_eq (i : ℕ) (d : Path) :
    Fb r a ε s i d * gsum κ L₀ α a r (Fb r a ε s) n i d =
      Fb r a ε s i d * LamB κ L₀ n α r a ε s i d := by
  rcases bs_eq_or r a ε s i d with h | h
  · congr 1
    unfold LamB gsum
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≤ j := (Finset.mem_Ico.mp hj).1
    rw [wF_Fb, bs_shift r a ε s i j hij d, h]
  · rw [h, zero_mul, zero_mul]

lemma LamB_abs (hα : 0 ≤ α) (i : ℕ) (d : Path) :
    |LamB κ L₀ n α r a ε s i d| ≤ ∑ j ∈ Finset.range n, α ^ j * max κ.b κ.h := by
  unfold LamB
  calc |∑ j ∈ Finset.Ico i n, α ^ j * gd κ (bsF r s i (sig a ε s i) d (j - i) - Sw L₀ d j)|
      ≤ ∑ j ∈ Finset.Ico i n,
          |α ^ j * gd κ (bsF r s i (sig a ε s i) d (j - i) - Sw L₀ d j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ico i n, α ^ j * max κ.b κ.h := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_of_nonneg (pow_nonneg hα j)]
        exact mul_le_mul_of_nonneg_left (gd_abs κ _) (pow_nonneg hα j)
    _ ≤ ∑ j ∈ Finset.range n, α ^ j * max κ.b κ.h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj; simp only [Finset.mem_Ico] at hj; simp only [Finset.mem_range]; omega
        · intro j _ _
          exact mul_nonneg (pow_nonneg hα j) (le_trans κ.b_pos.le (le_max_left _ _))

lemma LamB_loc (i : ℕ) (d : Path) :
    LamB κ L₀ n α r a ε s i d = LamB κ L₀ n α r a ε s i (trunc (Finset.Ico i (n + L₀)) d) := by
  unfold LamB
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have h1 : ∀ t < j - i, d (i + t) = trunc (Finset.Ico i (n + L₀)) d (i + t) := by
    intro t ht; unfold trunc; rw [if_pos (by simp only [Finset.mem_Ico]; omega)]
  have h2 : Sw L₀ d j = Sw L₀ (trunc (Finset.Ico i (n + L₀)) d) j := by
    unfold Sw
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    unfold trunc; rw [if_pos (by simp only [Finset.mem_Ico]; omega)]
  rw [bsF_loc r s i _ d _ (j - i) h1, h2]

lemma measurable_LamB (i : ℕ) : Measurable (LamB κ L₀ n α r a ε s i) := by
  unfold LamB
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul ((measurable_gd κ).comp
    ((measurable_bsF r s i _ (j - i)).sub (measurable_Sw L₀ j))))

end bsc

/-! ## choosing the levels -/

lemma exists_level {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, ∫ ω, max (c - X ω) 0 ∂P = ε := by
  set φ : ℝ → ℝ := fun c => ∫ ω, max (c - X ω) 0 ∂P with hφ
  have hint : ∀ c, Integrable (fun ω => max (c - X ω) 0) P := fun c =>
    ((integrable_const c).sub hX).pos_part
  have hlip : ∀ c c', |φ c - φ c'| ≤ |c - c'| := by
    intro c c'
    simp only [hφ]
    rw [← integral_sub (hint c) (hint c'), ← Real.norm_eq_abs]
    have hb : ∀ᵐ ω ∂P, ‖max (c - X ω) 0 - max (c' - X ω) 0‖ ≤ |c - c'| :=
      ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        have := abs_max_sub_max_le_abs (c - X ω) (c' - X ω) 0
        rwa [show c - X ω - (c' - X ω) = c - c' by ring] at this)
    have := norm_integral_le_of_norm_le_const hb
    simpa using this
  have hcont : Continuous φ := by
    have : LipschitzWith 1 φ := LipschitzWith.of_dist_le_mul (fun x y => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]; exact hlip x y)
    exact this.continuous
  set c1 : ℝ := ∫ ω, X ω ∂P + ε with hc1
  have hup : ε ≤ φ c1 := by
    have hi1 : Integrable (fun ω => c1 - X ω) P := (integrable_const c1).sub hX
    have h := integral_mono hi1 (hint c1)
      (fun ω => le_max_left (c1 - X ω) 0)
    rw [integral_sub (integrable_const c1) hX] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    simp only [hφ]
    linarith
  have hlim : Tendsto φ atBot (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun ω => |X ω|)
      (F := fun c ω => max (c - X ω) 0) (f := fun _ => (0 : ℝ)) (l := atBot)
      (Eventually.of_forall (fun c => (hint c).aestronglyMeasurable))
      (by
        filter_upwards [eventually_le_atBot (0 : ℝ)] with c hc
        exact ae_of_all _ (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          apply max_le _ (abs_nonneg _)
          linarith [neg_abs_le (X ω)]))
      hX.abs
      (ae_of_all _ (fun ω => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_le_atBot (X ω)] with c hc
        exact (max_eq_right (by linarith)).symm))
    simpa using h
  obtain ⟨c2, hc2⟩ := Filter.eventually_atBot.mp (hlim.eventually (gt_mem_nhds hε))
  have hlo : φ (min c2 c1) < ε := hc2 _ (min_le_left _ _)
  obtain ⟨c, _, hc⟩ := intermediate_value_Icc (min_le_right c2 c1) hcont.continuousOn
    ⟨hlo.le, hup⟩
  exact ⟨c, hc⟩

section levels

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : DemandLaw} {κ : Costs}
  {L₀ L : ℕ} {χ : Ω → Fin (L - L₀ - 1) → ℝ} {q : Ω → Fin (L - L₀) → ℝ} {I : Ω → ℝ}
  {D : ℕ → Ω → ℝ}

lemma integrable_bs (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (r : ℝ) (s : ℕ → ℝ)
    (z0 : ℝ) (k : ℕ) : Integrable (fun ω => bs r s z0 (Dv D ω) k) P := by
  have := hw.isProb
  have hg : Integrable (fun ω => |z0| + ∑ j ∈ Finset.range (k + 1), |s j| +
      ∑ j ∈ Finset.range k, (|r| + |D j ω|)) P :=
    (integrable_const _).add (integrable_finsetSum _ (fun j _ =>
      (integrable_const _).add (integrable_D hw j).abs))
  refine Integrable.mono' hg
    ((measurable_bs r s z0 k).comp (measurable_Dv D hw.measurable_D)).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  rw [Real.norm_eq_abs]
  exact bs_abs r s z0 (Dv D ω) k

lemma integrable_Fb (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (r a ε : ℝ) (s : ℕ → ℝ)
    (i : ℕ) : Integrable (fun ω => Fb r a ε s i (Dv D ω)) P := by
  have := hw.isProb
  cases i with
  | zero => exact integrable_const ε
  | succ i =>
    exact (integrable_bs hw r s _ (i + 1)).sub
      (((integrable_bs hw r s _ i).add (integrable_const r)).sub (integrable_D hw i))

lemma exists_levels (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (r a ε : ℝ) (hε : 0 < ε)
    (m : ℕ) : ∃ s : ℕ → ℝ, ∀ i, 1 ≤ i → i ≤ m → ∫ ω, Fb r a ε s i (Dv D ω) ∂P = ε := by
  have := hw.isProb
  induction m with
  | zero => exact ⟨fun _ => 0, fun i h1 h2 => by omega⟩
  | succ m ih =>
    obtain ⟨s, hs⟩ := ih
    have hX : Integrable (fun ω => bs r s (a + ε) (Dv D ω) m + r - D m ω) P :=
      ((integrable_bs hw r s _ m).add (integrable_const r)).sub (integrable_D hw m)
    obtain ⟨c, hc⟩ := exists_level _ hX ε hε
    refine ⟨Function.update s (m + 1) c, fun i h1 h2 => ?_⟩
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · refine Eq.trans ?_ (hs i h1 (by omega))
      congr 1; funext ω
      apply Fb_sloc
      intro j hj
      rw [Function.update_of_ne (by omega)]
    · obtain rfl : i = m + 1 := by omega
      refine Eq.trans ?_ hc
      congr 1; funext ω
      have hsl : bs r (Function.update s (m + 1) c) (a + ε) (Dv D ω) m =
          bs r s (a + ε) (Dv D ω) m :=
        bs_sloc r _ s _ _ m (fun j hj => by rw [Function.update_of_ne (by omega)])
      simp only [Fb, bs]
      rw [hsl, Function.update_self]
      rw [← max_sub_sub_right, sub_self, max_comm]
      rfl

end levels

end XGL2

namespace XGL2

open XinGoldbergTBS.Asymptotic

/-! ## the comparison policy as an `SSPolicy` -/

def extF (n : ℕ) (v : Fin n → ℝ) : Path := fun j => if h : j < n then v ⟨j, h⟩ else 0

lemma measurable_extF (n : ℕ) : Measurable (extF n) := by
  apply measurable_pi_lambda
  intro j
  unfold extF
  by_cases h : j < n
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma extF_eq (n : ℕ) (d : Path) : extF n (fun i : Fin n => d i) = trunc (Finset.range n) d := by
  funext j
  unfold extF trunc
  by_cases h : j < n <;> simp [h]

noncomputable def polOf (F : ℕ → Path → ℝ) (hFm : ∀ i, Measurable (F i)) : SSPolicy where
  order n v := (F n (extF n v)).toNNReal
  measurable_order n := measurable_real_toNNReal.comp ((hFm n).comp (measurable_extF n))

section pol

variable (F : ℕ → Path → ℝ) (hFm : ∀ i, Measurable (F i)) (hF0 : ∀ i d, 0 ≤ F i d)
  (hFloc : ∀ i d, F i d = F i (trunc (Finset.range i) d))
include hF0 hFloc

lemma ssOrder_polOf (d : Path) (i : ℕ) : ssOrder (polOf F hFm) d i = F i d := by
  unfold ssOrder polOf
  simp only
  rw [extF_eq, ← hFloc]
  exact Real.coe_toNNReal _ (hF0 i d)

lemma upTo_polOf (r x : ℝ) (d : Path) (k : ℕ) :
    ssOrderUpTo (polOf F hFm) r x d k =
      x + ∑ i ∈ Finset.range k, (r - d i) + ∑ i ∈ Finset.range (k + 1), F i d := by
  have hp : ∀ k, ssPosition (polOf F hFm) r x d k =
      x + ∑ i ∈ Finset.range k, (r - d i) + ∑ i ∈ Finset.range k, F i d := by
    intro k
    induction k with
    | zero => simp [ssPosition]
    | succ k ih =>
      simp only [ssPosition]
      rw [ih, ssOrder_polOf F hFm hF0 hFloc, Finset.sum_range_succ (fun i => r - d i),
        Finset.sum_range_succ (fun i => F i d)]
      ring
  unfold ssOrderUpTo
  rw [hp, ssOrder_polOf F hFm hF0 hFloc, Finset.sum_range_succ (fun i => F i d) k]
  ring

lemma ssCost_polOf (κ : Costs) (L₀ : ℕ) (a r : ℝ) (d : Path) (k : ℕ) :
    ssCost κ L₀ (polOf F hFm) r (a - (L₀ + 1) * r) d k =
      ENNReal.ofReal (G κ (wF L₀ a r F d k)) := by
  unfold ssCost
  rw [upTo_polOf F hFm hF0 hFloc]
  congr 2
  have hs : ∑ j ∈ Finset.range (L₀ + 1), (d (k + j) - r) =
      ∑ j ∈ Finset.range (L₀ + 1), d (k + j) - (L₀ + 1) * r := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hs]
  unfold wF Sw
  ring

end pol

lemma measurable_G (κ : Costs) : Measurable (G κ) := by
  unfold G
  exact (measurable_const.mul (measurable_id.max measurable_const)).add
    (measurable_const.mul (measurable_id.neg.max measurable_const))

lemma G_nonneg (κ : Costs) (y : ℝ) : 0 ≤ G κ y := by
  unfold G
  exact add_nonneg (mul_nonneg κ.h_pos.le (le_max_right _ _))
    (mul_nonneg κ.b_pos.le (le_max_right _ _))

section final

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : DemandLaw} {κ : Costs}
  {L₀ L : ℕ} {χ : Ω → Fin (L - L₀ - 1) → ℝ} {q : Ω → Fin (L - L₀) → ℝ} {I : Ω → ℝ}
  {D : ℕ → Ω → ℝ}

lemma map_Dv (hw : IsStationaryWitness P μ κ L₀ L χ q I D) : P.map (Dv D) = pathLaw μ := by
  have := hw.isProb
  have h := (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
    (fun i => (hw.measurable_D i).aemeasurable)).mp hw.indep_D
  simp only [hw.law_D] at h
  exact h

/-- some nonanticipative comparison policy is dominated by the witness -/
lemma exists_F (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (hL : L₀ + 1 < L)
    (α : ℝ) (hα : 0 ≤ α) :
    ∃ F : ℕ → Path → ℝ, ∃ hFm : (∀ i, Measurable (F i)), (∀ i d, 0 ≤ F i d) ∧
      (∀ i d, F i d = F i (trunc (Finset.range i) d)) ∧
      (∀ i, Integrable (fun ω => F i (Dv D ω)) P) ∧
      ∑ k ∈ Finset.range (L - L₀), α ^ k *
          ∫ ω, G κ (Wt L₀ (∫ ω, I ω ∂P) (rL P L₀ L χ) F D k ω) ∂P ≤
        ∑ k ∈ Finset.range (L - L₀), α ^ k * ∫ ω, G κ (Yk L₀ L χ q I D k ω) ∂P := by
  have := hw.isProb
  set a := ∫ ω, I ω ∂P with ha
  set r := rL P L₀ L χ with hr
  set ε := ∫ ω, qN L₀ L q ω 0 ∂P with hε
  set C := ∑ j ∈ Finset.range (L - L₀), α ^ j * max κ.b κ.h with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (pow_nonneg hα j) (le_trans κ.b_pos.le (le_max_left _ _)))
  have hε0 : 0 ≤ ε := by
    apply integral_nonneg_of_ae
    filter_upwards [hw.nonneg] with ω hω
    simp only [Pi.zero_apply, qN]
    split_ifs
    · exact hω.2 _
    · exact le_rfl
  rcases hε0.lt_or_eq with hεp | hεz
  · obtain ⟨s, hs⟩ := exists_levels hw r a ε hεp (L - L₀ - 1)
    refine ⟨Fb r a ε s, measurable_Fb r a ε s, Fb_nonneg r a ε s hε0, Fb_loc r a ε s,
      integrable_Fb hw r a ε s, ?_⟩
    refine core hw hL (L - L₀) rfl a r rfl rfl α hα (Fb r a ε s)
      (LamB κ L₀ (L - L₀) α r a ε s) C
      (measurable_Fb r a ε s) (Fb_nonneg r a ε s hε0) (Fb_loc r a ε s)
      (integrable_Fb hw r a ε s) ?_ (measurable_LamB κ L₀ (L - L₀) α r a ε s)
      (LamB_abs κ L₀ (L - L₀) α r a ε s hα) (LamB_loc κ L₀ (L - L₀) α r a ε s)
      (fun i _ d => LamB_le κ L₀ (L - L₀) α r a ε s hα i d)
      (fun i _ d => LamB_eq κ L₀ (L - L₀) α r a ε s i d)
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp [Fb]; try exact hε
    · exact hs i hpos (by omega)
  · refine ⟨fun _ _ => 0, fun _ => measurable_const, fun _ _ => le_rfl, fun _ _ => rfl,
      fun _ => integrable_const 0, ?_⟩
    refine core hw hL (L - L₀) rfl a r rfl rfl α hα (fun _ _ => 0) (fun _ _ => -C) C
      (fun _ => measurable_const) (fun _ _ => le_rfl) (fun _ _ => rfl)
      (fun _ => integrable_const 0) ?_ (fun _ => measurable_const)
      (fun _ _ => by rw [abs_neg, abs_of_nonneg hC0]) (fun _ _ => rfl) ?_ ?_
    · intro i _; simp only [integral_zero]; exact hεz
    · intro i _ d
      have := gsum_abs κ L₀ α a r hα (fun _ _ => 0) (L - L₀) i d
      linarith [neg_abs_le (gsum κ L₀ α a r (fun _ _ => 0) (L - L₀) i d)]
    · intro i _ d; simp

lemma main_bound (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (hL : L₀ + 1 < L)
    (α : ℝ) (hα : 0 ≤ α) :
    VnNegInf μ κ L₀ α (L - L₀) (rL P L₀ L χ) ≤
      ENNReal.ofReal (∑ k ∈ Finset.range (L - L₀), α ^ k *
        ∫ ω, G κ (Yk L₀ L χ q I D k ω) ∂P) := by
  have := hw.isProb
  obtain ⟨F, hFm, hF0, hFloc, hFint, hle⟩ := exists_F hw hL α hα
  set a := ∫ ω, I ω ∂P with ha
  set r := rL P L₀ L χ with hr
  have hWint : ∀ k, Integrable (fun ω => G κ (Wt L₀ a r F D k ω)) P := fun k =>
    integrable_G κ (integrable_Wt hw a r F hFint k)
  have hcost : ∫⁻ d, ∑ i ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ i) *
        ssCost κ L₀ (polOf F hFm) r (a - (L₀ + 1) * r) d i ∂pathLaw μ =
      ENNReal.ofReal (∑ k ∈ Finset.range (L - L₀), α ^ k *
        ∫ ω, G κ (Wt L₀ a r F D k ω) ∂P) := by
    have hmeas : Measurable (fun d : Path => ∑ i ∈ Finset.range (L - L₀),
        ENNReal.ofReal (α ^ i) * ENNReal.ofReal (G κ (wF L₀ a r F d i))) :=
      Finset.measurable_sum _ (fun i _ => (ENNReal.measurable_ofReal.comp
        ((measurable_G κ).comp (measurable_wF L₀ a r F hFm i))).const_mul _)
    have e1 : ∀ d, ∑ i ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ i) *
        ssCost κ L₀ (polOf F hFm) r (a - (L₀ + 1) * r) d i =
        ∑ i ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ i) *
          ENNReal.ofReal (G κ (wF L₀ a r F d i)) := by
      intro d
      apply Finset.sum_congr rfl; intro i _
      rw [ssCost_polOf F hFm hF0 hFloc κ L₀ a r d i]
    simp_rw [e1]
    rw [← map_Dv hw, lintegral_map hmeas (measurable_Dv D hw.measurable_D)]
    have e2 : ∀ ω, ∑ i ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ i) *
        ENNReal.ofReal (G κ (wF L₀ a r F (Dv D ω) i)) =
        ENNReal.ofReal (∑ i ∈ Finset.range (L - L₀), α ^ i * G κ (Wt L₀ a r F D i ω)) := by
      intro ω
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (pow_nonneg hα i) (G_nonneg κ _))]
      apply Finset.sum_congr rfl; intro i _
      rw [ENNReal.ofReal_mul (pow_nonneg hα i)]
      rfl
    simp_rw [e2]
    have hsumint : Integrable (fun ω => ∑ i ∈ Finset.range (L - L₀),
        α ^ i * G κ (Wt L₀ a r F D i ω)) P :=
      integrable_finsetSum _ (fun i _ => (hWint i).const_mul _)
    rw [← ofReal_integral_eq_lintegral_ofReal hsumint
      (ae_of_all _ (fun ω => Finset.sum_nonneg (fun i _ =>
        mul_nonneg (pow_nonneg hα i) (G_nonneg κ _))))]
    congr 1
    rw [integral_finsetSum _ (fun i _ => (hWint i).const_mul _)]
    apply Finset.sum_congr rfl; intro i _
    rw [integral_const_mul]
  calc VnNegInf μ κ L₀ α (L - L₀) r ≤ Vn μ κ L₀ α (L - L₀) r (a - (L₀ + 1) * r) :=
        iInf_le _ _
    _ ≤ ∫⁻ d, ∑ i ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ i) *
          ssCost κ L₀ (polOf F hFm) r (a - (L₀ + 1) * r) d i ∂pathLaw μ :=
        iInf_le (fun π : SSPolicy => ∫⁻ d, ∑ i ∈ Finset.range (L - L₀),
          ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r (a - (L₀ + 1) * r) d i ∂pathLaw μ) _
    _ = _ := hcost
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

lemma stat_eq (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (k : ℕ) (hk : k < L - L₀) :
    ∫ ω, G κ (Yk L₀ L χ q I D k ω) ∂P =
      ∫ ω, G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω) ∂P := by
  have e : Yk L₀ L χ q I D k = fun ω => I ω + ∑ i ∈ Finset.range k,
      (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω) + q ω ⟨k, hk⟩ -
        ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω := by
    funext ω
    unfold Yk
    rw [show qN L₀ L q ω k = q ω ⟨k, hk⟩ from dif_pos hk]
  have h := ((hw.stationary ⟨k, hk⟩).comp (measurable_G κ)).integral_eq
  simp only [Function.comp] at h
  simp only [e]
  exact h

end final

end XGL2

open MeasureTheory ProbabilityTheory Filter XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) * VnNegInf μ κ L₀ α (L - L₀) (rL P L₀ L χ)
      ≤ OPT μ κ L₀ L := by
  have := hw.isProb
  set e0 := ∫ ω, G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω) ∂P with he0
  set S := ∑ k ∈ Finset.range (L - L₀), α ^ k with hS
  have he0n : 0 ≤ e0 := integral_nonneg (fun ω => XGL2.G_nonneg κ _)
  have hsum : ∑ k ∈ Finset.range (L - L₀), α ^ k *
      ∫ ω, G κ (XGL2.Yk L₀ L χ q I D k ω) ∂P = S * e0 := by
    rw [hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [XGL2.stat_eq hw k (Finset.mem_range.mp hk)]
  have hb := XGL2.main_bound hw hL α hα0.le
  rw [hsum] at hb
  have hgeom : (1 - α) * S = 1 - α ^ (L - L₀) := by
    have h := geom_sum_mul α (L - L₀)
    rw [hS]
    linear_combination -h
  have hchain : ENNReal.ofReal (1 - α) * VnNegInf μ κ L₀ α (L - L₀) (rL P L₀ L χ) ≤
      ∫⁻ ω, ENNReal.ofReal (G κ (I ω + qN L₀ L q ω 0 -
        ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P := by
    calc ENNReal.ofReal (1 - α) * VnNegInf μ κ L₀ α (L - L₀) (rL P L₀ L χ)
        ≤ ENNReal.ofReal (1 - α) * ENNReal.ofReal (S * e0) := by gcongr
      _ = ENNReal.ofReal ((1 - α) * (S * e0)) := by
          rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 - α by linarith)]
      _ ≤ ENNReal.ofReal e0 := by
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_assoc, hgeom]
          have : 0 ≤ α ^ (L - L₀) := pow_nonneg hα0.le _
          nlinarith
      _ = _ := by
          rw [he0]
          apply ofReal_integral_eq_lintegral_ofReal
          · exact XGL2.integrable_G κ ((hw.integrable_I.add (XGL2.integrable_qN hw 0)).sub
              (integrable_finsetSum _ (fun i _ => XGL2.integrable_D hw i)))
          · exact ae_of_all _ (fun ω => XGL2.G_nonneg κ _)
  exact le_trans (add_le_add le_rfl hchain) hw.opt_ge
