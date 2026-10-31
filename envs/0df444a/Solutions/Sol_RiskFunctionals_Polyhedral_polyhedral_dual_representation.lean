-- Prove2me | solution 1 for RiskFunctionals.Polyhedral.polyhedral_dual_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:29:49.572624+00:00
-- url     : https://prove2.me/submissions/0a91a7d0-386b-4d9e-b740-421a81fc8aa1

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod
import Theorems.Thm_RiskFunctionals_Polyhedral_fenchel_moreau_step
import Theorems.Thm_RiskFunctionals_Polyhedral_conjugate_eq

noncomputable section
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open MeasureTheory RiskFunctionals.Polyhedral RiskFunctionals.Polyhedral.MultiPeriodData

namespace PDR

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma cone_zero {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) :
    (0 : Fin k → ℝ) ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j; simp

lemma cone_smul {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V) {r : ℝ} (hr : 0 ≤ r)
    {e : Fin k → ℝ} (he : e ∈ V) : r • e ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j
  rw [dotProduct_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hr (he j)

lemma cone_add {k : ℕ} {V : Set (Fin k → ℝ)} (h : IsPolyhedralCone V)
    {x y : Fin k → ℝ} (hx : x ∈ V) (hy : y ∈ V) : x + y ∈ V := by
  obtain ⟨m, a, rfl⟩ := h
  intro j
  rw [dotProduct_add]
  exact add_nonpos (hx j) (hy j)

lemma dot_memLp {P : Measure Ω} {p : ENNReal} {k : ℕ} {f : Ω → Fin k → ℝ} (hf : MemLp f p P)
    (w : Fin k → ℝ) : MemLp (fun ω => w ⬝ᵥ f ω) p P := by
  have : (fun ω => w ⬝ᵥ f ω) = fun ω => ∑ i, w i * f ω i := by
    funext ω; simp [dotProduct]
  rw [this]
  exact memLp_finsetSum _ fun i _ => (hf.eval i).const_mul (w i)

lemma dot_meas {m : MeasurableSpace Ω} {k : ℕ} {f : Ω → Fin k → ℝ} (hf : Measurable[m] f)
    (w : Fin k → ℝ) : Measurable[m] (fun ω => w ⬝ᵥ f ω) := by
  have hc : Continuous fun x : Fin k → ℝ => w ⬝ᵥ x := by
    simp only [dotProduct]; fun_prop
  exact hc.measurable.comp hf

lemma abs_dot_le {k : ℕ} (w v : Fin k → ℝ) {B : ℝ} (hB : ∀ i, |v i| ≤ B) :
    |w ⬝ᵥ v| ≤ (∑ i, |w i|) * B := by
  unfold dotProduct
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)

/-! ### Linear structure of the feasible set -/

lemma feas_zero (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} (hi : D.CompleteRecourse T) :
    D.Feasible P p T 𝓕 0 0 := by
  refine ⟨fun t ht => ⟨measurable_const, MemLp.zero, Filter.Eventually.of_forall fun ω =>
    cone_zero (hi.1 t ht)⟩, fun t ht => Filter.Eventually.of_forall fun ω => by simp⟩

lemma feas_comb (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} (hi : D.CompleteRecourse T) {Y Y' : ℕ → Ω → ℝ}
    {v v' : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) (hv' : D.Feasible P p T 𝓕 Y' v') {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    D.Feasible P p T 𝓕 (a • Y + b • Y') (a • v + b • v') := by
  refine ⟨fun t ht => ⟨?_, ?_, ?_⟩, fun t ht => ?_⟩
  · have h1 := (hv.1 t ht).1
    have h2 := (hv'.1 t ht).1
    show Measurable[𝓕 t] (fun ω => a • v t ω + b • v' t ω)
    fun_prop
  · exact ((hv.1 t ht).2.1.const_smul a).add ((hv'.1 t ht).2.1.const_smul b)
  · filter_upwards [(hv.1 t ht).2.2, (hv'.1 t ht).2.2] with ω h1 h2
    exact cone_add (hi.1 t ht) (cone_smul (hi.1 t ht) ha h1) (cone_smul (hi.1 t ht) hb h2)
  · filter_upwards [hv.2 t ht, hv'.2 t ht] with ω h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]

lemma obj_comb (D : MultiPeriodData) {P : Measure Ω} [IsFiniteMeasure P] {p : ENNReal}
    (hp : 1 ≤ p) {T : ℕ} {𝓕 : ℕ → MeasurableSpace Ω} {Y Y' : ℕ → Ω → ℝ}
    {v v' : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) (hv' : D.Feasible P p T 𝓕 Y' v') (a b : ℝ) :
    D.objective P T (a • v + b • v') = a * D.objective P T v + b * D.objective P T v' := by
  unfold objective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ T := by simp at hs; omega
  have i1 := (dot_memLp (hv.1 s hs').2.1 (D.c s)).integrable hp
  have i2 := (dot_memLp (hv'.1 s hs').2.1 (D.c s)).integrable hp
  simp only [Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul, integral_const_mul]

/-! ### Real-valued version of the sup -/

lemma le_F (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} {v : (t : ℕ) → Ω → Fin (D.k t) → ℝ}
    (hv : D.Feasible P p T 𝓕 Y v) (htop : D.functional P p T 𝓕 Y ≠ ⊤) :
    D.objective P T v ≤ (D.functional P p T 𝓕 Y).toReal := by
  have h : ((D.objective P T v : ℝ) : EReal) ≤ D.functional P p T 𝓕 Y :=
    le_sSup ⟨v, hv, rfl⟩
  have := EReal.toReal_le_toReal h (EReal.coe_ne_bot _) htop
  simpa using this

lemma F_le (D : MultiPeriodData) {P : Measure Ω} {p : ENNReal} {T : ℕ}
    {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} (hbot : D.functional P p T 𝓕 Y ≠ ⊥)
    {c : ℝ} (h : ∀ v, D.Feasible P p T 𝓕 Y v → D.objective P T v ≤ c) :
    (D.functional P p T 𝓕 Y).toReal ≤ c := by
  have h1 : D.functional P p T 𝓕 Y ≤ (c : EReal) := by
    refine sSup_le ?_
    rintro x ⟨v, hv, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (h v hv)
  have := EReal.toReal_le_toReal h1 hbot (EReal.coe_ne_top _)
  simpa using this

lemma scale_le {F : ℝ} {S : ℝ → Prop} (hL2 : ∀ c, (∀ x, S x → x ≤ c) → F ≤ c)
    (hex : ∃ x, S x) {a c : ℝ} (ha : 0 ≤ a) (h : ∀ x, S x → a * x ≤ c) : a * F ≤ c := by
  rcases ha.eq_or_lt with rfl | ha
  · obtain ⟨x, hx⟩ := hex
    simpa using h x hx
  · have : F ≤ c / a := hL2 _ fun x hx => by
      rw [le_div_iff₀ ha, mul_comm]; exact h x hx
    rw [le_div_iff₀ ha, mul_comm] at this
    exact this

/-! ### Explicit feasible solution (complete recourse) -/

/-- The recursively defined feasible decision process. -/
def vv (D : MultiPeriodData) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) (Y : ℕ → Ω → ℝ) :
    (t : ℕ) → Ω → Fin (D.k t) → ℝ
  | t => fun ω =>
    let x := Y t ω - ∑ s ∈ (Finset.range t).attach, D.W t s.1 ⬝ᵥ vv D ep em Y s.1 ω
    ((|x| + x) / 2) • ep t + ((|x| - x) / 2) • em t
termination_by t => t
decreasing_by exact Finset.mem_range.mp s.2

def xval (D : MultiPeriodData) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) (Y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  Y t ω - ∑ s ∈ Finset.range t, D.W t s ⬝ᵥ vv D ep em Y s ω

lemma vv_eq (D : MultiPeriodData) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) (Y : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    vv D ep em Y t ω = ((|xval D ep em Y t ω| + xval D ep em Y t ω) / 2) • ep t +
      ((|xval D ep em Y t ω| - xval D ep em Y t ω) / 2) • em t := by
  rw [vv]
  simp only [xval]
  rw [Finset.sum_attach (Finset.range t) (fun s => D.W t s ⬝ᵥ vv D ep em Y s ω)]


structure GoodE (D : MultiPeriodData) (T : ℕ) (ep em : (t : ℕ) → Fin (D.k t) → ℝ) : Prop where
  zero_p : ep 0 = 0
  zero_m : em 0 = 0
  mem_p : ∀ t ∈ Finset.Icc 1 T, ep t ∈ D.V t
  mem_m : ∀ t ∈ Finset.Icc 1 T, em t ∈ D.V t
  dot_p : ∀ t ∈ Finset.Icc 1 T, D.W t t ⬝ᵥ ep t = 1
  dot_m : ∀ t ∈ Finset.Icc 1 T, D.W t t ⬝ᵥ em t = -1

lemma exists_goodE (D : MultiPeriodData) {T : ℕ} (hi : D.CompleteRecourse T) :
    ∃ ep em, GoodE D T ep em := by
  have h : ∀ t, ∃ e : (Fin (D.k t) → ℝ) × (Fin (D.k t) → ℝ),
      (t = 0 → e.1 = 0 ∧ e.2 = 0) ∧ (t ∈ Finset.Icc 1 T → e.1 ∈ D.V t ∧ e.2 ∈ D.V t ∧
        D.W t t ⬝ᵥ e.1 = 1 ∧ D.W t t ⬝ᵥ e.2 = -1) := by
    intro t
    by_cases ht : t ∈ Finset.Icc 1 T
    · have hs := hi.2 t ht
      have h1 : (1 : ℝ) ∈ (fun v => D.W t t ⬝ᵥ v) '' D.V t := hs ▸ Set.mem_univ _
      have h2 : (-1 : ℝ) ∈ (fun v => D.W t t ⬝ᵥ v) '' D.V t := hs ▸ Set.mem_univ _
      obtain ⟨a, ha, ha'⟩ := h1
      obtain ⟨b, hb, hb'⟩ := h2
      refine ⟨(a, b), fun h0 => ?_, fun _ => ⟨ha, hb, ha', hb'⟩⟩
      simp [h0] at ht
    · exact ⟨(0, 0), fun _ => ⟨rfl, rfl⟩, fun h => absurd h ht⟩
  choose e he using h
  exact ⟨fun t => (e t).1, fun t => (e t).2, ⟨((he 0).1 rfl).1, ((he 0).1 rfl).2,
    fun t ht => ((he t).2 ht).1, fun t ht => ((he t).2 ht).2.1,
    fun t ht => ((he t).2 ht).2.2.1, fun t ht => ((he t).2 ht).2.2.2⟩⟩

section
variable {D : MultiPeriodData} {T : ℕ} {ep em : (t : ℕ) → Fin (D.k t) → ℝ}

lemma vv_zero (hE : GoodE D T ep em) (Y : ℕ → Ω → ℝ) (ω : Ω) : vv D ep em Y 0 ω = 0 := by
  rw [vv_eq, hE.zero_p, hE.zero_m]; simp

lemma vv_dot (hE : GoodE D T ep em) (Y : ℕ → Ω → ℝ) {t : ℕ} (ht : t ∈ Finset.Icc 1 T)
    (ω : Ω) : D.W t t ⬝ᵥ vv D ep em Y t ω = xval D ep em Y t ω := by
  rw [vv_eq, dotProduct_add, dotProduct_smul, dotProduct_smul, hE.dot_p t ht, hE.dot_m t ht]
  simp only [smul_eq_mul]; ring

lemma vv_constr (hE : GoodE D T ep em) (Y : ℕ → Ω → ℝ) {t : ℕ} (ht : t ∈ Finset.Icc 1 T)
    (ω : Ω) : ∑ s ∈ Finset.range (t + 1), D.W t s ⬝ᵥ vv D ep em Y s ω = Y t ω := by
  rw [Finset.sum_range_succ, vv_dot hE Y ht, xval]; ring

lemma vv_mem (hE : GoodE D T ep em) (hi : D.CompleteRecourse T) (Y : ℕ → Ω → ℝ) {t : ℕ}
    (ht : t ≤ T) (ω : Ω) : vv D ep em Y t ω ∈ D.V t := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · rw [vv_zero hE]; exact cone_zero (hi.1 0 ht)
  · have ht' : t ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨hpos, ht⟩
    rw [vv_eq]
    set x := xval D ep em Y t ω
    have h1 : 0 ≤ (|x| + x) / 2 := by have := neg_abs_le x; linarith
    have h2 : 0 ≤ (|x| - x) / 2 := by have := le_abs_self x; linarith
    exact cone_add (hi.1 t ht) (cone_smul (hi.1 t ht) h1 (hE.mem_p t ht'))
      (cone_smul (hi.1 t ht) h2 (hE.mem_m t ht'))

lemma vv_meas (hE : GoodE D T ep em) {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : IsFiltrationUpTo mΩ T 𝓕)
    {Y : ℕ → Ω → ℝ} (hY : ∀ t ∈ Finset.Icc 1 T, Measurable[𝓕 t] (Y t)) :
    ∀ t, t ≤ T → Measurable[𝓕 t] (vv D ep em Y t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · have : vv D ep em Y 0 = fun _ => 0 := funext fun ω => vv_zero hE Y ω
      rw [this]; exact measurable_const
    · have ht' : t ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨hpos, ht⟩
      have hx : Measurable[𝓕 t] (xval D ep em Y t) := by
        have hs : ∀ s ∈ Finset.range t,
            Measurable[𝓕 t] (fun ω => D.W t s ⬝ᵥ vv D ep em Y s ω) := by
          intro s hs
          have hs' : s < t := Finset.mem_range.mp hs
          exact (dot_meas (IH s hs' (by omega)) _).mono (h𝓕.2.1 s t hs'.le ht) le_rfl
        exact (hY t ht').sub (Finset.measurable_fun_sum _ hs)
      have : vv D ep em Y t = fun ω =>
          ((|xval D ep em Y t ω| + xval D ep em Y t ω) / 2) • ep t +
          ((|xval D ep em Y t ω| - xval D ep em Y t ω) / 2) • em t :=
        funext fun ω => vv_eq D ep em Y t ω
      rw [this]
      fun_prop

/-- `S Y ω = Σ_{t=1}^T |Y_t(ω)|`. -/
def Ssum (T : ℕ) (Y : ℕ → Ω → ℝ) (ω : Ω) : ℝ := ∑ t ∈ Finset.Icc 1 T, |Y t ω|

lemma Ssum_nonneg (T : ℕ) (Y : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ Ssum T Y ω :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma vv_bound (hE : GoodE D T ep em) :
    ∃ C, 0 ≤ C ∧ ∀ (Y : ℕ → Ω → ℝ) (t : ℕ), t ≤ T → ∀ ω i,
      |vv D ep em Y t ω i| ≤ C * Ssum T Y ω := by
  suffices h : ∀ n, ∃ C, 0 ≤ C ∧ ∀ (Y : ℕ → Ω → ℝ) (t : ℕ), t ≤ n → t ≤ T → ∀ ω i,
      |vv D ep em Y t ω i| ≤ C * Ssum T Y ω by
    obtain ⟨C, hC, h⟩ := h T
    exact ⟨C, hC, fun Y t ht => h Y t ht ht⟩
  intro n
  induction n with
  | zero =>
    refine ⟨0, le_rfl, fun Y t ht _ ω i => ?_⟩
    have : t = 0 := by omega
    subst this
    rw [vv_zero hE]; simp
  | succ n IH =>
    obtain ⟨C, hC, hb⟩ := IH
    set A := ∑ s ∈ Finset.range (n + 1), ∑ i, |D.W (n + 1) s i|
    set E := ∑ i, (|ep (n + 1) i| + |em (n + 1) i|)
    have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => by positivity
    refine ⟨C + (1 + A * C) * E, by positivity, fun Y t ht hT ω i => ?_⟩
    have hS := Ssum_nonneg T Y ω
    rcases Nat.lt_or_ge t (n + 1) with hlt | hge
    · refine (hb Y t (by omega) hT ω i).trans ?_
      have : 0 ≤ (1 + A * C) * E * Ssum T Y ω := by positivity
      nlinarith
    · have htn : t = n + 1 := by omega
      subst htn
      have hmem : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hT⟩
      -- bound on x
      have hx : |xval D ep em Y (n + 1) ω| ≤ (1 + A * C) * Ssum T Y ω := by
        unfold xval
        have h1 : |Y (n + 1) ω| ≤ Ssum T Y ω :=
          Finset.single_le_sum (f := fun t => |Y t ω|) (fun _ _ => abs_nonneg _) hmem
        have h2 : |∑ s ∈ Finset.range (n + 1), D.W (n + 1) s ⬝ᵥ vv D ep em Y s ω| ≤
            A * (C * Ssum T Y ω) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun s hs => ?_
          have hs' : s ≤ n := by simp at hs; omega
          exact abs_dot_le _ _ fun j => hb Y s hs' (by omega) ω j
        calc |Y (n + 1) ω - ∑ s ∈ Finset.range (n + 1), D.W (n + 1) s ⬝ᵥ vv D ep em Y s ω|
            ≤ |Y (n + 1) ω| + |∑ s ∈ Finset.range (n + 1), D.W (n + 1) s ⬝ᵥ
                vv D ep em Y s ω| := abs_sub _ _
          _ ≤ Ssum T Y ω + A * (C * Ssum T Y ω) := add_le_add h1 h2
          _ = (1 + A * C) * Ssum T Y ω := by ring
      rw [vv_eq]
      set x := xval D ep em Y (n + 1) ω
      have ha1 : 0 ≤ (|x| + x) / 2 := by have := neg_abs_le x; linarith
      have ha2 : (|x| + x) / 2 ≤ |x| := by have := le_abs_self x; linarith
      have hb1 : 0 ≤ (|x| - x) / 2 := by have := le_abs_self x; linarith
      have hb2 : (|x| - x) / 2 ≤ |x| := by have := neg_abs_le x; linarith
      have hEi : |ep (n + 1) i| + |em (n + 1) i| ≤ E :=
        Finset.single_le_sum (f := fun i => |ep (n + 1) i| + |em (n + 1) i|)
          (fun _ _ => by positivity) (Finset.mem_univ i)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |(|x| + x) / 2 * ep (n + 1) i + (|x| - x) / 2 * em (n + 1) i|
          ≤ |(|x| + x) / 2 * ep (n + 1) i| + |(|x| - x) / 2 * em (n + 1) i| := abs_add_le _ _
        _ = (|x| + x) / 2 * |ep (n + 1) i| + (|x| - x) / 2 * |em (n + 1) i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha1, abs_of_nonneg hb1]
        _ ≤ |x| * |ep (n + 1) i| + |x| * |em (n + 1) i| := by
            gcongr
        _ = |x| * (|ep (n + 1) i| + |em (n + 1) i|) := by ring
        _ ≤ ((1 + A * C) * Ssum T Y ω) * E := by
            gcongr
        _ ≤ (C + (1 + A * C) * E) * Ssum T Y ω := by nlinarith

lemma Ssum_memLp {P : Measure Ω} {p : ENNReal} {𝓕 : ℕ → MeasurableSpace Ω} {Y : ℕ → Ω → ℝ}
    (hY : IsAdaptedLp P p T 𝓕 Y) : MemLp (Ssum T Y) p P := by
  have : Ssum T Y = fun ω => ∑ t ∈ Finset.Icc 1 T, ‖Y t ω‖ := by
    funext ω; simp [Ssum, Real.norm_eq_abs]
  rw [this]
  exact memLp_finsetSum _ fun t ht => (hY t ht).2.norm

lemma vv_feas (hE : GoodE D T ep em) (hi : D.CompleteRecourse T) {P : Measure Ω}
    {p : ENNReal} {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : IsFiltrationUpTo mΩ T 𝓕)
    {Y : ℕ → Ω → ℝ} (hY : IsAdaptedLp P p T 𝓕 Y) :
    D.Feasible P p T 𝓕 Y (vv D ep em Y) := by
  obtain ⟨C, hC, hb⟩ := vv_bound (Ω := Ω) hE
  have hm := vv_meas hE h𝓕 (fun t ht => (hY t ht).1)
  refine ⟨fun t ht => ⟨hm t ht, ?_, Filter.Eventually.of_forall fun ω => vv_mem hE hi Y ht ω⟩,
    fun t ht => Filter.Eventually.of_forall fun ω => vv_constr hE Y ht ω⟩
  refine MemLp.of_le ((Ssum_memLp hY).const_mul C)
    ((hm t ht).mono (h𝓕.2.2 t ht) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ C * Ssum T Y ω := mul_nonneg hC (Ssum_nonneg T Y ω)
  rw [Real.norm_of_nonneg h0]
  refine (pi_norm_le_iff_of_nonneg h0).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact hb Y t ht ω i

lemma obj_lb (hE : GoodE D T ep em) {P : Measure Ω} [IsProbabilityMeasure P] {p : ENNReal}
    (hp : 1 ≤ p) :
    ∃ K, 0 ≤ K ∧ ∀ {𝓕 : ℕ → MeasurableSpace Ω} (Y : ℕ → Ω → ℝ),
      IsFiltrationUpTo mΩ T 𝓕 → IsAdaptedLp P p T 𝓕 Y →
      -(K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |Y t ω| ∂P) ≤ D.objective P T (vv D ep em Y) := by
  obtain ⟨C, hC, hb⟩ := vv_bound (Ω := Ω) hE
  set a : ℕ → ℝ := fun t => ∑ i, |D.c t i|
  have ha : ∀ t, 0 ≤ a t := fun t => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C * ∑ t ∈ Finset.range (T + 1), a t,
    mul_nonneg hC (Finset.sum_nonneg fun t _ => ha t), fun {𝓕} Y h𝓕 hY => ?_⟩
  have hSi : Integrable (Ssum T Y) P := (Ssum_memLp hY).integrable hp
  have hIS : ∫ ω, Ssum T Y ω ∂P = ∑ t ∈ Finset.Icc 1 T, ∫ ω, |Y t ω| ∂P := by
    unfold Ssum
    rw [integral_finsetSum]
    intro t ht
    exact ((hY t ht).2.integrable hp).abs
  rw [← hIS]
  unfold objective
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht' : t ≤ T := by simp at ht; omega
  have hg : Integrable (fun ω => a t * (C * Ssum T Y ω)) P := (hSi.const_mul C).const_mul _
  have hle := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun ω =>
    (show ‖D.c t ⬝ᵥ vv D ep em Y t ω‖ ≤ a t * (C * Ssum T Y ω) by
      rw [Real.norm_eq_abs]
      exact abs_dot_le _ _ fun i => hb Y t ht' ω i))
  rw [integral_const_mul, integral_const_mul, Real.norm_eq_abs] at hle
  have := neg_abs_le (∫ ω, D.c t ⬝ᵥ vv D ep em Y t ω ∂P)
  have e : C * (a t * ∫ ω, Ssum T Y ω ∂P) = a t * (C * ∫ ω, Ssum T Y ω ∂P) := by ring
  rw [e]
  linarith
end

end PDR

namespace PDR

lemma int_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {p : ENNReal} (hp : 1 ≤ p) {f : Ω → ℝ} (hf : MemLp f p P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlt : eLpNorm f p P < ENNReal.ofReal δ) : ∫ ω, |f ω| ∂P ≤ δ := by
  have h1 : eLpNorm f 1 P ≤ eLpNorm f p P := eLpNorm_le_eLpNorm_of_exponent_le hp hf.1
  have h2 := (lt_of_le_of_lt h1 hlt).le
  have e : ∫ ω, |f ω| ∂P = (eLpNorm f 1 P).toReal := by
    rw [show (fun ω => |f ω|) = fun ω => ‖f ω‖ from funext fun ω => (Real.norm_eq_abs _).symm,
      integral_norm_eq_lintegral_enorm hf.1, ← eLpNorm_one_eq_lintegral_enorm]
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal hδ h2

end PDR

open PDR in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) (hii : D.DualFeasible T) :
    (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
    PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
    ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
    ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
    InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
    (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y =
        sInf {x : EReal | ∃ Z ∈ D.dualSet P q T 𝓕, x = (pairing P T Y Z : EReal)}) := by
  -- (3.55): Fenchel–Moreau step combined with the conjugate formula (3.59)
  have hdual : ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y =
        sInf {x : EReal | ∃ Z ∈ D.dualSet P q T 𝓕, x = (pairing P T Y Z : EReal)} := by
    intro Y hY
    have hce := conjugate_eq P p q hp hp_top hpq T hT 𝓕 h𝓕 D hD hi hii
    rw [fenchel_moreau_step P p q hp hp_top hpq T hT 𝓕 h𝓕 D hD hi hii Y hY]
    apply le_antisymm
    · refine le_sInf ?_
      rintro x ⟨Z, hZ, rfl⟩
      refine sInf_le ⟨Z, hZ.1, ?_⟩
      rw [(hce Z hZ.1).1 hZ, sub_zero]
    · refine le_sInf ?_
      rintro x ⟨Z, hZq, rfl⟩
      by_cases hZ : Z ∈ D.dualSet P q T 𝓕
      · refine sInf_le_of_le ⟨Z, hZ, rfl⟩ ?_
        rw [(hce Z hZq).1 hZ, sub_zero]
      · rw [(hce Z hZq).2 hZ, EReal.coe_sub_bot]
        exact le_top
  -- a point of the dual set: the constant process `ū`
  obtain ⟨u, hu0, hut⟩ := id hii
  have hZbar : (fun τ (_ : Ω) => u τ) ∈ D.dualSet P q T 𝓕 := by
    refine ⟨fun t ht => ⟨measurable_const, memLp_const _⟩, ?_, fun t ht => ?_⟩
    · simpa using hu0
    · have hle : 𝓕 t ≤ mΩ := h𝓕.2.2 t (Finset.mem_Icc.mp ht).2
      refine Filter.Eventually.of_forall fun ω => ?_
      simp only [condExp_const hle]
      exact hut t ht
  -- the explicit feasible solution
  obtain ⟨ep, em, hE⟩ := exists_goodE D hi
  have hfin : ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤ := by
    intro Y hY
    constructor
    · have h : ((D.objective P T (vv D ep em Y) : ℝ) : EReal) ≤ D.functional P p T 𝓕 Y :=
        le_sSup ⟨_, vv_feas hE hi h𝓕 hY, rfl⟩
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
    · rw [hdual Y hY]
      exact ne_top_of_le_ne_top (EReal.coe_ne_top (pairing P T Y (fun τ (_ : Ω) => u τ)))
        (sInf_le ⟨_, hZbar, rfl⟩)
  -- real-valued sup
  set F : (ℕ → Ω → ℝ) → ℝ := fun Y => (D.functional P p T 𝓕 Y).toReal with hFdef
  have hL1 : ∀ Y v, IsAdaptedLp P p T 𝓕 Y → D.Feasible P p T 𝓕 Y v →
      D.objective P T v ≤ F Y := fun Y v hY hv => le_F D hv (hfin Y hY).2
  have hL2 : ∀ Y, IsAdaptedLp P p T 𝓕 Y → ∀ c : ℝ,
      (∀ x, (∃ v, D.Feasible P p T 𝓕 Y v ∧ D.objective P T v = x) → x ≤ c) → F Y ≤ c :=
    fun Y hY c h => F_le D (hfin Y hY).1 fun v hv => h _ ⟨v, hv, rfl⟩
  have hex : ∀ Y, IsAdaptedLp P p T 𝓕 Y →
      ∃ x, ∃ v, D.Feasible P p T 𝓕 Y v ∧ D.objective P T v = x :=
    fun Y hY => ⟨_, _, vv_feas hE hi h𝓕 hY, rfl⟩
  have hAd : ∀ Y Y', IsAdaptedLp P p T 𝓕 Y → IsAdaptedLp P p T 𝓕 Y' → ∀ a b : ℝ,
      IsAdaptedLp P p T 𝓕 (a • Y + b • Y') := by
    intro Y Y' hY hY' a b t ht
    have h1 := (hY t ht).1
    have h2 := (hY' t ht).1
    refine ⟨?_, ((hY t ht).2.const_smul a).add ((hY' t ht).2.const_smul b)⟩
    show Measurable[𝓕 t] (fun ω => a • Y t ω + b • Y' t ω)
    fun_prop
  have hzero : IsAdaptedLp P p T 𝓕 (0 : ℕ → Ω → ℝ) := fun t ht =>
    ⟨measurable_const, MemLp.zero⟩
  have hcomb : ∀ Y Y', IsAdaptedLp P p T 𝓕 Y → IsAdaptedLp P p T 𝓕 Y' → ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a * F Y + b * F Y' ≤ F (a • Y + b • Y') := by
    intro Y Y' hY hY' a b ha hb
    have hmix := hAd Y Y' hY hY' a b
    have key : ∀ v v', D.Feasible P p T 𝓕 Y v → D.Feasible P p T 𝓕 Y' v' →
        a * D.objective P T v + b * D.objective P T v' ≤ F (a • Y + b • Y') := by
      intro v v' hv hv'
      rw [← obj_comb D hp hv hv' a b]
      exact hL1 _ _ hmix (feas_comb D hi hv hv' ha hb)
    have step1 : ∀ v', D.Feasible P p T 𝓕 Y' v' →
        a * F Y + b * D.objective P T v' ≤ F (a • Y + b • Y') := by
      intro v' hv'
      have := scale_le (hL2 Y hY) (hex Y hY) ha
        (c := F (a • Y + b • Y') - b * D.objective P T v') (by
          rintro x ⟨v, hv, rfl⟩
          linarith [key v v' hv hv'])
      linarith
    have := scale_le (hL2 Y' hY') (hex Y' hY') hb (c := F (a • Y + b • Y') - a * F Y) (by
      rintro x ⟨v', hv', rfl⟩
      linarith [step1 v' hv'])
    linarith
  refine ⟨hfin, ?_, ?_, ?_, ?_, hdual⟩
  · -- positive homogeneity
    intro Y hY lam hlam
    have hY' : IsAdaptedLp P p T 𝓕 (lam • Y) := by
      have := hAd Y 0 hY hzero lam 0
      rwa [zero_smul, add_zero] at this
    apply le_antisymm
    · have h := hcomb (lam • Y) 0 hY' hzero lam⁻¹ 0 (inv_nonneg.mpr hlam.le) le_rfl
      rw [zero_smul, add_zero, zero_mul, add_zero, smul_smul, inv_mul_cancel₀ hlam.ne',
        one_smul] at h
      exact (inv_mul_le_iff₀ hlam).mp h
    · have h := hcomb Y 0 hY hzero lam 0 hlam.le le_rfl
      rwa [zero_smul, add_zero, zero_mul, add_zero] at h
  · -- concavity
    intro Y Y' hY hY' lam h0 h1
    exact hcomb Y Y' hY hY' lam (1 - lam) h0 (by linarith)
  · -- continuity
    obtain ⟨K, hK, hlb⟩ := obj_lb hE (P := P) hp
    have hFlb : ∀ Y, IsAdaptedLp P p T 𝓕 Y →
        -(K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |Y t ω| ∂P) ≤ F Y := fun Y hY =>
      (hlb Y h𝓕 hY).trans (hL1 _ _ hY (vv_feas hE hi h𝓕 hY))
    intro Y hY ε hε
    have hKT : 0 ≤ K * T := mul_nonneg hK (Nat.cast_nonneg T)
    refine ⟨ε / (K * T + 1), div_pos hε (by linarith), fun Y' hY' hd => ?_⟩
    set δ := ε / (K * T + 1) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hε (by linarith)).le
    have hΔ : IsAdaptedLp P p T 𝓕 (Y' - Y) := fun t ht =>
      ⟨(hY' t ht).1.sub (hY t ht).1, (hY' t ht).2.sub (hY t ht).2⟩
    have hΔ' : IsAdaptedLp P p T 𝓕 (Y - Y') := fun t ht =>
      ⟨(hY t ht).1.sub (hY' t ht).1, (hY t ht).2.sub (hY' t ht).2⟩
    have hs1 : ∑ t ∈ Finset.Icc 1 T, ∫ ω, |(Y' - Y) t ω| ∂P ≤ T * δ := by
      calc ∑ t ∈ Finset.Icc 1 T, ∫ ω, |(Y' - Y) t ω| ∂P ≤ ∑ t ∈ Finset.Icc 1 T, δ :=
            Finset.sum_le_sum fun t ht => int_abs_le hp (hΔ t ht).2 hδ0 (hd t ht)
        _ = T * δ := by simp
    have hs2 : ∑ t ∈ Finset.Icc 1 T, ∫ ω, |(Y - Y') t ω| ∂P ≤ T * δ := by
      refine le_of_eq_of_le (Finset.sum_congr rfl fun t _ => integral_congr_ae
        (Filter.Eventually.of_forall fun ω => ?_)) hs1
      simp only [Pi.sub_apply]
      exact abs_sub_comm _ _
    have e1 : (1 : ℝ) • Y + (1 : ℝ) • (Y' - Y) = Y' := by rw [one_smul, one_smul, add_sub_cancel]
    have e2 : (1 : ℝ) • Y' + (1 : ℝ) • (Y - Y') = Y := by rw [one_smul, one_smul, add_sub_cancel]
    have c1 := hcomb Y (Y' - Y) hY hΔ 1 1 zero_le_one zero_le_one
    have c2 := hcomb Y' (Y - Y') hY' hΔ' 1 1 zero_le_one zero_le_one
    rw [e1] at c1
    rw [e2] at c2
    have l1 := hFlb _ hΔ
    have l2 := hFlb _ hΔ'
    have m1 : K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |(Y' - Y) t ω| ∂P ≤ K * (T * δ) :=
      mul_le_mul_of_nonneg_left hs1 hK
    have m2 : K * ∑ t ∈ Finset.Icc 1 T, ∫ ω, |(Y - Y') t ω| ∂P ≤ K * (T * δ) :=
      mul_le_mul_of_nonneg_left hs2 hK
    have hlt : K * (T * δ) < ε := by
      rw [hδ, ← mul_assoc, mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    show |F Y' - F Y| < ε
    rw [abs_lt]
    constructor <;> linarith
  · -- (MA0)
    intro 𝓖 𝓖' _ _ hle Y _
    refine sSup_le_sSup ?_
    rintro x ⟨v, hv, rfl⟩
    exact ⟨v, ⟨fun t ht => ⟨(hv.1 t ht).1.mono (hle t ht) le_rfl, (hv.1 t ht).2⟩, hv.2⟩, rfl⟩
