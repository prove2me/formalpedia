-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P05.energyBoundNowhereDense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:46:14.795279+00:00
-- url     : https://prove2.me/submissions/5189adbc-9469-40f8-a796-552fb51514e7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05
noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)


open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsTraceClass)

theorem g74l_coef_hasSum {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (i j : I) :
    HasSum (fun n => e.left n i * star (e.right n j)) (X i j) := by
  have hb : ∀ n, ‖e.left n i * star (e.right n j)‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
      (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable (fun n => e.left n i * star (e.right n j)) :=
    Summable.of_norm_bounded e.summable hb
  rw [e.coefficients i j]
  exact hs.hasSum

def g74l_expAdd {I : Type} {X Y : Matrix I I ℂ} (eX : NuclearExpansion X)
    (eY : NuclearExpansion Y) : NuclearExpansion (X + Y) where
  left n := if n % 2 = 0 then eX.left (n / 2) else eY.left (n / 2)
  right n := if n % 2 = 0 then eX.right (n / 2) else eY.right (n / 2)
  summable := by
    apply Summable.even_add_odd
    · refine eX.summable.congr (fun k => ?_)
      have h1 : (2 * k) % 2 = 0 := by omega
      have h2 : 2 * k / 2 = k := by omega
      simp [h1, h2]
    · refine eY.summable.congr (fun k => ?_)
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      simp [h1, h2]
  coefficients i j := by
    rw [Matrix.add_apply]
    symm
    apply HasSum.tsum_eq
    apply HasSum.even_add_odd
    · refine (g74l_coef_hasSum eX i j).congr_fun (fun k => ?_)
      have h1 : (2 * k) % 2 = 0 := by omega
      have h2 : 2 * k / 2 = k := by omega
      simp [h1, h2]
    · refine (g74l_coef_hasSum eY i j).congr_fun (fun k => ?_)
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      simp [h1, h2]

theorem g74l_expAdd_sum {I : Type} {X Y : Matrix I I ℂ} (eX : NuclearExpansion X)
    (eY : NuclearExpansion Y) :
    ∑' n, ‖(g74l_expAdd eX eY).left n‖ * ‖(g74l_expAdd eX eY).right n‖ =
      ∑' n, ‖eX.left n‖ * ‖eX.right n‖ + ∑' n, ‖eY.left n‖ * ‖eY.right n‖ := by
  apply HasSum.tsum_eq
  apply HasSum.even_add_odd
  · refine eX.summable.hasSum.congr_fun (fun k => ?_)
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    simp [g74l_expAdd, h1, h2]
  · refine eY.summable.hasSum.congr_fun (fun k => ?_)
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp [g74l_expAdd, h1, h2]

def g74l_expSmul {I : Type} {X : Matrix I I ℂ} (c : ℂ) (e : NuclearExpansion X) :
    NuclearExpansion (c • X) where
  left n := c • e.left n
  right n := e.right n
  summable := by
    simp only [norm_smul, mul_assoc]
    exact e.summable.mul_left _
  coefficients i j := by
    rw [Matrix.smul_apply, e.coefficients i j, smul_eq_mul, ← tsum_mul_left]
    congr 1; funext n
    simp [mul_assoc]

theorem g74l_expSmul_sum {I : Type} {X : Matrix I I ℂ} (c : ℂ) (e : NuclearExpansion X) :
    ∑' n, ‖(g74l_expSmul c e).left n‖ * ‖(g74l_expSmul c e).right n‖ =
      ‖c‖ * ∑' n, ‖e.left n‖ * ‖e.right n‖ := by
  simp only [g74l_expSmul, norm_smul, mul_assoc]
  exact tsum_mul_left

def g74l_expCast {I : Type} {X Y : Matrix I I ℂ} (h : X = Y) (e : NuclearExpansion X) :
    NuclearExpansion Y where
  left := e.left
  right := e.right
  summable := e.summable
  coefficients i j := by rw [← h]; exact e.coefficients i j

theorem g74l_ts_le {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    traceSize X ≤ ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖) := iInf_le _ e

theorem g74l_ts_add {I : Type} (X Y : Matrix I I ℂ) :
    traceSize (X + Y) ≤ traceSize X + traceSize Y := by
  unfold traceSize
  rw [ENNReal.iInf_add]
  refine le_iInf fun eX => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun eY => ?_
  refine (iInf_le _ (g74l_expAdd eX eY)).trans (le_of_eq ?_)
  rw [g74l_expAdd_sum, ENNReal.ofReal_add (tsum_nonneg fun _ => by positivity)
    (tsum_nonneg fun _ => by positivity)]

theorem g74l_coef_le {I : Type} (X : Matrix I I ℂ) (i j : I) :
    ENNReal.ofReal ‖X i j‖ ≤ traceSize X := by
  unfold traceSize
  refine le_iInf fun e => ENNReal.ofReal_le_ofReal ?_
  rw [e.coefficients i j]
  have hb : ∀ n, ‖e.left n i * star (e.right n j)‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
      (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable (fun n => ‖e.left n i * star (e.right n j)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb e.summable
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb e.summable)

theorem g74l_traceSize_zero {I : Type} : traceSize (0 : Matrix I I ℂ) = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le (⟨fun _ => 0, fun _ => 0, by simp, by intro i j; simp⟩ :
    NuclearExpansion (0 : Matrix I I ℂ)) ?_
  simp

def g74l_e {I : Type} (i : I) : Hilbert I := lp.single 2 i (1 : ℂ)

theorem g74l_e_apply {I : Type} (i a : I) : g74l_e i a = if a = i then 1 else 0 := by
  simp [g74l_e, lp.single_apply, Pi.single_apply]

theorem g74l_e_norm {I : Type} (i : I) : ‖g74l_e i‖ = 1 := by
  simp [g74l_e, lp.norm_single (p := 2) (by norm_num)]

def g74l_exp2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) : NuclearExpansion X where
  left n := if n = 0 then u else if n = 1 then u' else 0
  right n := if n = 0 then v else if n = 1 then v' else 0
  summable := by
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [h0, h1]
  coefficients i j := by
    rw [hX, tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      simp [h0, h1]

theorem g74l_ts2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) :
    traceSize X ≤ ENNReal.ofReal (‖u‖ * ‖v‖ + ‖u'‖ * ‖v'‖) := by
  refine (iInf_le _ (g74l_exp2 X u v u' v' hX)).trans (le_of_eq ?_)
  congr 1
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [g74l_exp2, Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [g74l_exp2, h0, h1]

def g74l_P {I : Type} (i : I) : Matrix I I ℂ := fun a b => g74l_e i a * star (g74l_e i b)

theorem g74l_P_apply {I : Type} (i a b : I) : g74l_P i a b = if a = i ∧ b = i then 1 else 0 := by
  simp only [g74l_P, g74l_e_apply]
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb]

theorem g74l_P_density {I : Type} (i : I) : IsDensity (g74l_P i) := by
  refine ⟨⟨g74l_exp2 _ (g74l_e i) (g74l_e i) 0 0 (fun a b => by simp [g74l_P])⟩, ?_, ?_, ?_⟩
  · intro s z
    have : (∑ a ∈ s, ∑ b ∈ s, star (z a) * g74l_P i a b * z b) =
        star (∑ b ∈ s, star (g74l_e i b) * z b) * (∑ b ∈ s, star (g74l_e i b) * z b) := by
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      simp only [g74l_P, star_mul, star_star]
      ring
    rw [this]
    set S := ∑ b ∈ s, star (g74l_e i b) * z b
    have h := Complex.conj_mul' S
    rw [show star S = (starRingEnd ℂ) S from rfl, h]
    constructor
    · norm_cast
    · norm_cast; positivity
  · apply summable_of_ne_finset_zero (s := {i})
    intro a ha
    simp only [Finset.mem_singleton] at ha
    simp [g74l_P_apply, ha]
  · rw [tsum_eq_single i]
    · simp [g74l_P_apply]
    · intro a ha; simp [g74l_P_apply, ha]

def g74l_pure {I : Type} (i : I) : State I := ⟨g74l_P i, g74l_P_density i⟩


theorem g74l_mix_density {I : Type} (ρ ω : State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsDensity ((((1 - t : ℝ)) : ℂ) • ρ.coefficients + ((t : ℝ) : ℂ) • ω.coefficients) := by
  obtain ⟨eρ⟩ := ρ.density.1
  obtain ⟨eω⟩ := ω.density.1
  refine ⟨⟨g74l_expAdd (g74l_expSmul _ eρ) (g74l_expSmul _ eω)⟩, ?_, ?_, ?_⟩
  · intro s z
    obtain ⟨h1, h2⟩ := ρ.density.2.1 s z
    obtain ⟨h3, h4⟩ := ω.density.2.1 s z
    have : (∑ i ∈ s, ∑ j ∈ s, star (z i) *
        ((((1 - t : ℝ)) : ℂ) • ρ.coefficients + ((t : ℝ) : ℂ) • ω.coefficients) i j * z j) =
        (((1 - t : ℝ)) : ℂ) * (∑ i ∈ s, ∑ j ∈ s, star (z i) * ρ.coefficients i j * z j) +
        ((t : ℝ) : ℂ) * (∑ i ∈ s, ∑ j ∈ s, star (z i) * ω.coefficients i j * z j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [this]
    simp only [Complex.add_im, Complex.add_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      h1, h3, mul_zero, add_zero]
    refine ⟨trivial, ?_⟩
    have : 0 ≤ 1 - t := by linarith
    positivity
  · have := (ρ.density.2.2.1.mul_left (1 - t)).add (ω.density.2.2.1.mul_left t)
    refine this.congr (fun i => ?_)
    simp [Matrix.add_apply, Matrix.smul_apply]
  · have e1 : ∀ i, ((((((1 - t : ℝ)) : ℂ) • ρ.coefficients + ((t : ℝ) : ℂ) • ω.coefficients)) i i).re
        = (1 - t) * (ρ.coefficients i i).re + t * (ω.coefficients i i).re := by
      intro i; simp [Matrix.add_apply, Matrix.smul_apply]
    simp only [e1]
    rw [Summable.tsum_add (ρ.density.2.2.1.mul_left _) (ω.density.2.2.1.mul_left _), tsum_mul_left,
      tsum_mul_left, ρ.density.2.2.2, ω.density.2.2.2]
    ring

def g74l_ball {I : Type} (σ : State I) (δ : ℝ) : Set (State I) :=
  {x | traceSize (x.coefficients - σ.coefficients) < ENNReal.ofReal δ}

theorem g74l_ball_mono {I : Type} (σ : State I) {δ δ' : ℝ} (h : δ ≤ δ') :
    g74l_ball σ δ ⊆ g74l_ball σ δ' := fun x hx =>
  lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal h)

theorem g74l_open_ball {I : Type} (U : Set (State I)) (hU : IsOpen U) :
    ∀ σ ∈ U, ∃ δ > 0, g74l_ball σ δ ⊆ U := by
  change TopologicalSpace.GenerateOpen _ U at hU
  induction hU with
  | basic s hs =>
    obtain ⟨ρ', ε, hε, rfl⟩ := hs
    intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ
    set a := traceSize (σ.coefficients - ρ'.coefficients)
    have hpos : 0 < ENNReal.ofReal ε - a := tsub_pos_of_lt hσ
    have hfin : ENNReal.ofReal ε - a ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
    refine ⟨(ENNReal.ofReal ε - a).toReal, ENNReal.toReal_pos hpos.ne' hfin, ?_⟩
    intro x hx
    simp only [g74l_ball, Set.mem_setOf_eq, ENNReal.ofReal_toReal hfin] at hx ⊢
    calc traceSize (x.coefficients - ρ'.coefficients)
        = traceSize ((x.coefficients - σ.coefficients) + (σ.coefficients - ρ'.coefficients)) := by
          rw [sub_add_sub_cancel]
      _ ≤ traceSize (x.coefficients - σ.coefficients) + a := g74l_ts_add _ _
      _ < ENNReal.ofReal ε := lt_tsub_iff_right.mp hx
  | univ => intro σ _; exact ⟨1, one_pos, Set.subset_univ _⟩
  | inter s t _ _ ihs iht =>
    intro σ hσ
    obtain ⟨δ1, h1, hb1⟩ := ihs σ hσ.1
    obtain ⟨δ2, h2, hb2⟩ := iht σ hσ.2
    exact ⟨min δ1 δ2, lt_min h1 h2, fun x hx =>
      ⟨hb1 (g74l_ball_mono σ (min_le_left _ _) hx), hb2 (g74l_ball_mono σ (min_le_right _ _) hx)⟩⟩
  | sUnion S _ ih =>
    intro σ hσ
    obtain ⟨s, hs, hσs⟩ := hσ
    obtain ⟨δ, hδ, hb⟩ := ih s hs σ hσs
    exact ⟨δ, hδ, hb.trans (Set.subset_sUnion_of_mem hs)⟩

theorem g74l_unbdd (h : HamiltonianData) (C : ℝ) : ∃ p, C < levelEnergy h p := by
  by_contra hc
  push_neg at hc
  have hs := h.gibbs 1 one_pos
  have : Summable (fun _ : ℕ × ℕ => Real.exp (-C)) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
      (fun p => Real.exp_le_exp.mpr (by have := hc p; simp only [levelEnergy] at this; linarith)) hs
  rw [summable_const_iff] at this
  exact (Real.exp_pos _).ne' this

theorem solution (h : HamiltonianData) (M : ℝ) (hM : 0 < M) :
    interior (closure (energyBound h M)) = ∅ := by
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hρ
  obtain ⟨δ, hδ, hball⟩ := g74l_open_ball _ isOpen_interior ρ hρ
  obtain ⟨eρ⟩ := ρ.density.1
  set L := levelEnergy h (0, 0) with hL
  set sρ := ∑' n, ‖eρ.left n‖ * ‖eρ.right n‖ with hsρ
  have hsρ0 : 0 ≤ sρ := tsum_nonneg fun _ => by positivity
  -- the perturbing basis state will have expansion sum sω; bound uniformly below
  set t : ℝ := min (1 / 2) (δ / (2 * (sρ + 2))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htδ : t * (sρ + 2) < δ := by
    have : t ≤ δ / (2 * (sρ + 2)) := min_le_right _ _
    have h2 : δ / (2 * (sρ + 2)) * (sρ + 2) = δ / 2 := by field_simp
    nlinarith
  obtain ⟨p, hp⟩ := g74l_unbdd h (L + 2 * |M - L| / t + 1)
  let ω : State (ℕ × ℕ) := g74l_pure p
  let eω : NuclearExpansion ω.coefficients :=
    g74l_exp2 (g74l_P p) (g74l_e p) (g74l_e p) 0 0 (fun a b => by simp [g74l_P])
  have hsω : ∑' n, ‖eω.left n‖ * ‖eω.right n‖ ≤ 2 := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [eω, g74l_exp2, Finset.sum_range_succ, g74l_e_norm]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      simp [eω, g74l_exp2, h0, h1]
  let τ : State (ℕ × ℕ) := ⟨(((1 - t : ℝ)) : ℂ) • ρ.coefficients + ((t : ℝ) : ℂ) • ω.coefficients,
    g74l_mix_density ρ ω t ht0.le ht1⟩
  have hτ : τ ∈ g74l_ball ρ δ := by
    have hmat : τ.coefficients - ρ.coefficients =
        ((t : ℝ) : ℂ) • (ω.coefficients + (-1 : ℂ) • ρ.coefficients) := by
      show (((1 - t : ℝ)) : ℂ) • ρ.coefficients + ((t : ℝ) : ℂ) • ω.coefficients - ρ.coefficients = _
      push_cast
      module
    let e1 := g74l_expCast hmat.symm (g74l_expSmul ((t : ℝ) : ℂ) (g74l_expAdd eω (g74l_expSmul (-1) eρ)))
    show traceSize (τ.coefficients - ρ.coefficients) < ENNReal.ofReal δ
    refine lt_of_le_of_lt (g74l_ts_le e1) ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr ?_)
    have : ∑' n, ‖e1.left n‖ * ‖e1.right n‖ =
        t * (∑' n, ‖eω.left n‖ * ‖eω.right n‖ + sρ) := by
      show ∑' n, ‖(g74l_expSmul ((t : ℝ) : ℂ) (g74l_expAdd eω (g74l_expSmul (-1) eρ))).left n‖ *
        ‖(g74l_expSmul ((t : ℝ) : ℂ) (g74l_expAdd eω (g74l_expSmul (-1) eρ))).right n‖ = _
      rw [g74l_expSmul_sum, g74l_expAdd_sum, g74l_expSmul_sum]
      simp [abs_of_pos ht0, ← hsρ]
    rw [this]
    nlinarith
  have hτc : τ ∈ closure (energyBound h M) := interior_subset (hball hτ)
  rw [mem_closure_iff] at hτc
  obtain ⟨σ, hσB, hσE⟩ := hτc (g74l_ball τ (t / 2))
    (TopologicalSpace.isOpen_generateFrom_of_mem ⟨τ, t / 2, by positivity, rfl⟩)
    (by
      show traceSize (τ.coefficients - τ.coefficients) < ENNReal.ofReal (t / 2)
      rw [sub_self, g74l_traceSize_zero]
      exact ENNReal.ofReal_pos.mpr (by positivity))
  have h1 : ‖(σ.coefficients - τ.coefficients) p p‖ < t / 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
      (lt_of_le_of_lt (g74l_coef_le _ p p) hσB)
  have hρpp : 0 ≤ (ρ.coefficients p p).re := by
    have := (ρ.density.2.1 {p} (fun _ => 1)).2
    simpa using this
  have hωpp : ω.coefficients p p = 1 := by
    show g74l_P p p p = 1
    simp [g74l_P_apply]
  have hτpp : t ≤ (τ.coefficients p p).re := by
    show t ≤ (((((1 - t : ℝ)) : ℂ) • ρ.coefficients + ((t : ℝ) : ℂ) • ω.coefficients) p p).re
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hωpp, Complex.add_re,
      Complex.re_ofReal_mul, Complex.one_re, mul_one, Complex.ofReal_re]
    have : 0 ≤ 1 - t := by linarith
    nlinarith
  have hσpp : t / 2 < (σ.coefficients p p).re := by
    have := Complex.abs_re_le_norm ((σ.coefficients - τ.coefficients) p p)
    rw [Matrix.sub_apply, Complex.sub_re] at this
    have := (abs_le.mp this).1
    rw [Matrix.sub_apply] at h1
    linarith [abs_le.mp (le_of_lt (lt_of_le_of_lt (Complex.abs_re_le_norm _) h1))]
  have hEp : L ≤ levelEnergy h p :=
    add_le_add (h.orderedA (Nat.zero_le _)) (h.orderedB (Nat.zero_le _))
  have hterm : ENNReal.ofReal ((levelEnergy h p - L) * (t / 2)) ≤
      ∑' i, ENNReal.ofReal ((levelEnergy h i - L) * (σ.coefficients i i).re) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hσpp.le (by linarith))).trans
      (ENNReal.le_tsum (f := fun i => ENNReal.ofReal ((levelEnergy h i - L) * (σ.coefficients i i).re)) p)
  have hbig : M - L < (levelEnergy h p - L) * (t / 2) := by
    have h2 : 2 * |M - L| / t * t = 2 * |M - L| := by field_simp
    have h3 := le_abs_self (M - L)
    nlinarith
  have hσE' : (L : EReal) + ((∑' i, ENNReal.ofReal ((levelEnergy h i - L) *
      (σ.coefficients i i).re)) : ℝ≥0∞).toEReal < (M : EReal) := hσE
  have hge : (((L + (levelEnergy h p - L) * (t / 2)) : ℝ) : EReal) ≤ (L : EReal) +
      ((∑' i, ENNReal.ofReal ((levelEnergy h i - L) * (σ.coefficients i i).re)) : ℝ≥0∞).toEReal := by
    rw [EReal.coe_add]
    gcongr
    have := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hterm
    rw [EReal.coe_ennreal_ofReal, max_eq_left (by nlinarith)] at this
    exact this
  have hlt : (M : EReal) < (((L + (levelEnergy h p - L) * (t / 2)) : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by linarith)
  exact lt_irrefl _ (hσE'.trans (hlt.trans_le hge))

end
