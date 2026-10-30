-- Prove2me | solution 1 for TaoBR.nikodymSetConjecture_of_kakeyaSetConjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:17:59.339757+00:00
-- url     : https://prove2.me/submissions/275a3ad1-c25e-4956-a834-38c69825bf02

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

open Metric Filter Topology

namespace NK

/-! ## Covering numbers -/

theorem exists_cover {n : ℕ} {A : Set (E n)} (hA : Bornology.IsBounded A) {r : ℝ} (hr : 0 < r) :
    ∃ k, ∃ c : Fin k → E n, A ⊆ ⋃ i, ball (c i) r := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact hA.isCompact_closure hr
  have : Finite t := ht.to_subtype
  obtain ⟨k, ⟨f⟩⟩ := Finite.exists_equiv_fin t
  refine ⟨k, fun j => (f.symm j : E n), ?_⟩
  intro x hx
  have := hcov (subset_closure hx)
  simp only [Set.mem_iUnion] at this
  obtain ⟨y, hy, hxy⟩ := this
  exact Set.mem_iUnion.2 ⟨f ⟨y, hy⟩, by simpa using hxy⟩

theorem cn_le {n : ℕ} {A : Set (E n)} {r : ℝ} {k : ℕ} (c : Fin k → E n)
    (h : A ⊆ ⋃ i, ball (c i) r) : coveringNumber A r ≤ k :=
  Nat.sInf_le ⟨c, h⟩

theorem cn_spec {n : ℕ} {A : Set (E n)} (hA : Bornology.IsBounded A) {r : ℝ} (hr : 0 < r) :
    ∃ c : Fin (coveringNumber A r) → E n, A ⊆ ⋃ i, ball (c i) r := by
  obtain ⟨k, c, h⟩ := exists_cover hA hr
  exact Nat.sInf_mem (s := {k : ℕ | ∃ c : Fin k → E n, A ⊆ ⋃ i, ball (c i) r}) ⟨k, c, h⟩

theorem one_le_cn {n : ℕ} {A : Set (E n)} (hA : Bornology.IsBounded A) (hne : A.Nonempty)
    {r : ℝ} (hr : 0 < r) : 1 ≤ coveringNumber A r := by
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := cn_spec hA hr
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hc hx)
  have := i.2
  omega

theorem cn_mono {n : ℕ} {A B : Set (E n)} (hAB : A ⊆ B) (hB : Bornology.IsBounded B)
    {r : ℝ} (hr : 0 < r) : coveringNumber A r ≤ coveringNumber B r := by
  obtain ⟨c, hc⟩ := cn_spec hB hr
  exact cn_le c (hAB.trans hc)

theorem cn_image_le {n : ℕ} {A : Set (E n)} (hA : Bornology.IsBounded A) (f : E n → E n)
    {L : ℝ} (hL : 0 < L) (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ L * dist x y)
    {r : ℝ} (hr : 0 < r) : coveringNumber (f '' A) (2 * L * r) ≤ coveringNumber A r := by
  classical
  obtain ⟨c, hc⟩ := cn_spec hA hr
  let p : Fin (coveringNumber A r) → E n := fun j =>
    if h : (A ∩ ball (c j) r).Nonempty then h.choose else c j
  refine cn_le (fun j => f (p j)) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hc hx)
  have hne : (A ∩ ball (c j) r).Nonempty := ⟨x, hx, hj⟩
  refine Set.mem_iUnion.2 ⟨j, ?_⟩
  have hp : p j = hne.choose := dif_pos hne
  have h1 := hne.choose_spec
  rw [mem_ball, hp]
  rw [mem_ball] at hj
  have h1' : dist hne.choose (c j) < r := h1.2
  calc dist (f x) (f hne.choose) ≤ L * dist x hne.choose := hf _ hx _ h1.1
    _ < L * (2 * r) := by
        apply mul_lt_mul_of_pos_left _ hL
        calc dist x hne.choose ≤ dist x (c j) + dist hne.choose (c j) := dist_triangle_right _ _ _
         _ < r + r := add_lt_add hj h1'
         _ = 2 * r := by ring
    _ = 2 * L * r := by ring

theorem cn_iUnion_le {n m : ℕ} (A : Fin m → Set (E n)) (hA : ∀ i, Bornology.IsBounded (A i))
    {r : ℝ} (hr : 0 < r) : coveringNumber (⋃ i, A i) r ≤ ∑ i, coveringNumber (A i) r := by
  choose c hc using fun i => cn_spec (hA i) hr
  refine cn_le (fun j => c (finSigmaFinEquiv.symm j).1 (finSigmaFinEquiv.symm j).2) ?_
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hc i hi)
  refine Set.mem_iUnion.2 ⟨finSigmaFinEquiv ⟨i, j⟩, ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hj

theorem isBounded_image_of_lip {n : ℕ} {A : Set (E n)} (hA : Bornology.IsBounded A)
    (f : E n → E n) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ L * dist x y) :
    Bornology.IsBounded (f '' A) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hA
  refine Metric.isBounded_iff.2 ⟨L * C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (hf x hx y hy).trans (mul_le_mul_of_nonneg_left (hC hx hy) hL)

/-! ## Dimension comparison -/

/-- The function whose liminf/limsup are the Minkowski dimensions. -/
noncomputable def dfun {n : ℕ} (A : Set (E n)) (r : ℝ) : ℝ :=
  Real.log (coveringNumber A r) / Real.log (1 / r)

theorem isBoundedUnder_le_of_limsup_ne {u : ℝ → ℝ} {F : Filter ℝ} (h : limsup u F ≠ 0) :
    IsBoundedUnder (· ≤ ·) F u := by
  by_contra hb
  apply h
  rw [Filter.limsup_eq]
  have : {a | ∀ᶠ x in F, u x ≤ a} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro ha
    exact hb ⟨a, ha⟩
  rw [this, Real.sInf_empty]

theorem dfun_nonneg {n : ℕ} {A : Set (E n)} (hA : Bornology.IsBounded A) (hne : A.Nonempty) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 ≤ dfun A r := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have h1 : (1 : ℝ) ≤ coveringNumber A r := by exact_mod_cast one_le_cn hA hne hr.1
  have h2 : 0 < Real.log (1 / r) := Real.log_pos ((one_lt_div hr.1).2 hr.2)
  exact div_nonneg (Real.log_nonneg h1) h2.le

theorem tendsto_log_inv : Tendsto (fun r : ℝ => Real.log (1 / r)) (𝓝[>] 0) atTop := by
  exact (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).congr
    (fun r => by simp only [Function.comp_apply, one_div])

theorem tendsto_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hc hr

theorem dims_eq {n : ℕ} (hn : (n : ℝ) ≠ 0) {S K B : Set (E n)}
    (hS : Bornology.IsBounded S) (hSne : S.Nonempty)
    (hK : Bornology.IsBounded K) (hKne : K.Nonempty)
    (hB : Bornology.IsBounded B) (hSB : S ⊆ B)
    (hKd : lowerMinkowskiDim K = n ∧ upperMinkowskiDim K = n)
    (hBd : lowerMinkowskiDim B = n ∧ upperMinkowskiDim B = n)
    {c : ℝ} (hc : 1 ≤ c) {M : ℕ} (hM : 1 ≤ M)
    (hcmp : ∀ r, 0 < r → coveringNumber K (c * r) ≤ M * coveringNumber S r) :
    lowerMinkowskiDim S = n ∧ upperMinkowskiDim S = n := by
  have hBne : B.Nonempty := hSne.mono hSB
  have hc0 : 0 < c := by linarith
  -- rewrite dims in terms of dfun
  have eL : ∀ A : Set (E n), lowerMinkowskiDim A = liminf (dfun A) (𝓝[>] 0) := fun _ => rfl
  have eU : ∀ A : Set (E n), upperMinkowskiDim A = limsup (dfun A) (𝓝[>] 0) := fun _ => rfl
  rw [eL, eU] at hKd hBd ⊢
  obtain ⟨hKl, hKu⟩ := hKd
  obtain ⟨hBl, hBu⟩ := hBd
  have hS0 := dfun_nonneg hS hSne
  have hK0 := dfun_nonneg hK hKne
  have hB0 := dfun_nonneg hB hBne
  obtain ⟨CB, hCB⟩ := isBoundedUnder_le_of_limsup_ne (u := dfun B) (F := 𝓝[>] 0) (by rw [hBu]; exact hn)
  obtain ⟨CK, hCK⟩ := isBoundedUnder_le_of_limsup_ne (u := dfun K) (F := 𝓝[>] 0) (by rw [hKu]; exact hn)
  have hCB' : ∀ᶠ r in 𝓝[>] (0 : ℝ), dfun B r ≤ CB := hCB
  have hCK' : ∀ᶠ r in 𝓝[>] (0 : ℝ), dfun K r ≤ CK := hCK
  have hSBle : ∀ᶠ r in 𝓝[>] (0 : ℝ), dfun S r ≤ dfun B r := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have h1 : (1 : ℝ) ≤ coveringNumber S r := by exact_mod_cast one_le_cn hS hSne hr.1
    have h3 : (coveringNumber S r : ℝ) ≤ coveringNumber B r := by
      exact_mod_cast cn_mono hSB hB hr.1
    have h2 : 0 < Real.log (1 / r) :=
      Real.log_pos ((one_lt_div hr.1).2 hr.2)
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) h3) h2.le
  -- bounds for dfun S
  have hSup : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (dfun S) :=
    ⟨CB, show ∀ᶠ r in 𝓝[>] (0 : ℝ), dfun S r ≤ CB by
      filter_upwards [hSBle, hCB'] with r h1 h2; exact h1.trans h2⟩
  have hSlo : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) (dfun S) := ⟨0, hS0⟩
  have hKlo : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) (dfun K) := ⟨0, hK0⟩
  have hBlo : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) (dfun B) := ⟨0, hB0⟩
  have hBup : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (dfun B) := ⟨CB, hCB'⟩
  -- key comparison
  have hmul := tendsto_mul_nhdsGT hc0
  have key : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), dfun K (c * r) - ε ≤ dfun S r := by
    intro ε hε
    have hlim : Tendsto (fun r : ℝ => (CK * Real.log c + Real.log M) / Real.log (1 / r))
        (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_inv
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / c by positivity),
      hmul.eventually hCK', hmul.eventually hK0, (tendsto_order.1 hlim).2 ε hε]
      with r hr hrK hrK0 hrε
    have hr0 : 0 < r := hr.1
    have hcr1 : c * r < 1 := by
      have := hr.2; rw [lt_div_iff₀ hc0] at this; linarith
    have hr1 : r < 1 := by nlinarith
    have hℓ : 0 < Real.log (1 / r) :=
      Real.log_pos ((one_lt_div hr0).2 hr1)
    have hℓc : 0 < Real.log (1 / (c * r)) :=
      Real.log_pos ((one_lt_div (by positivity)).2 hcr1)
    have hℓeq : Real.log (1 / (c * r)) = Real.log (1 / r) - Real.log c := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hc0.ne' hr0.ne']; ring
    have hN1 : (1 : ℝ) ≤ coveringNumber K (c * r) := by
      exact_mod_cast one_le_cn hK hKne (by positivity)
    have hN2 : (1 : ℝ) ≤ coveringNumber S r := by exact_mod_cast one_le_cn hS hSne hr0
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hcmp' : (coveringNumber K (c * r) : ℝ) ≤ M * coveringNumber S r := by
      exact_mod_cast hcmp r hr0
    have hlog : Real.log (coveringNumber K (c * r)) ≤ Real.log M + Real.log (coveringNumber S r) := by
      rw [← Real.log_mul (by linarith) (by linarith)]
      exact Real.log_le_log (by linarith) hcmp'
    have hKeq : dfun K (c * r) * Real.log (1 / (c * r)) = Real.log (coveringNumber K (c * r)) := by
      unfold dfun; field_simp
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hε' : CK * Real.log c + Real.log M ≤ ε * Real.log (1 / r) := by
      rw [div_lt_iff₀ hℓ] at hrε; linarith
    unfold dfun at hrK hrK0
    have hprod : dfun K (c * r) * Real.log c ≤ CK * Real.log c :=
      mul_le_mul_of_nonneg_right hrK hlc
    show dfun K (c * r) - ε ≤ Real.log (coveringNumber S r) / Real.log (1 / r)
    rw [le_div_iff₀ hℓ]
    rw [hℓeq] at hKeq
    have hlM : 0 ≤ Real.log M := Real.log_nonneg hM1
    nlinarith
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · -- liminf S ≤ n
    refine le_of_forall_pos_le_add fun ε hε => ?_
    apply liminf_le_of_frequently_le _ hSlo
    have hfr := frequently_lt_of_liminf_lt (hBup.isCoboundedUnder_flip)
      (show liminf (dfun B) (𝓝[>] 0) < n + ε by rw [hBl]; linarith)
    exact (hfr.and_eventually hSBle).mono fun r ⟨h1, h2⟩ => by linarith
  · -- n ≤ liminf S
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := eventually_lt_of_lt_liminf
      (show (n : ℝ) - ε / 2 < liminf (dfun K) (𝓝[>] 0) by rw [hKl]; linarith) hKlo
    have h2 := hmul.eventually h1
    have : (n : ℝ) - ε ≤ liminf (dfun S) (𝓝[>] 0) := by
      apply le_liminf_of_le hSup.isCoboundedUnder_flip
      filter_upwards [h2, key (ε / 2) (by linarith)] with r hr1 hr2
      linarith
    linarith
  · -- limsup S ≤ n
    refine le_of_forall_pos_le_add fun ε hε => ?_
    apply limsup_le_of_le hSlo.isCoboundedUnder_flip
    have h1 := eventually_lt_of_limsup_lt
      (show limsup (dfun B) (𝓝[>] 0) < n + ε by rw [hBu]; linarith) hBup
    filter_upwards [h1, hSBle] with r hr1 hr2
    linarith
  · -- n ≤ limsup S
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := frequently_lt_of_lt_limsup hKlo.isCoboundedUnder_flip
      (show (n : ℝ) - ε / 2 < limsup (dfun K) (𝓝[>] 0) by rw [hKu]; linarith)
    have hdiv : Tendsto (fun r : ℝ => r / c) (𝓝[>] 0) (𝓝[>] 0) := by
      simpa [div_eq_inv_mul] using tendsto_mul_nhdsGT (inv_pos.2 hc0)
    have h2 : ∃ᶠ r in 𝓝[>] (0 : ℝ), (n : ℝ) - ε / 2 < dfun K (c * r) := by
      apply hdiv.frequently
      refine h1.mono fun r hr => ?_
      simpa [mul_div_cancel₀ r hc0.ne'] using hr
    have : (n : ℝ) - ε ≤ limsup (dfun S) (𝓝[>] 0) := by
      apply le_limsup_of_frequently_le _ hSup
      exact (h2.and_eventually (key (ε / 2) (by linarith))).mono fun r ⟨h1, h2⟩ => by linarith
    linarith

/-! ## The projective charts -/

/-- The projective map `y ↦ ⟪y,e⟫⁻¹ (y + (1 - ⟪y,e⟫) e)`. -/
noncomputable def proj {n : ℕ} (e y : E n) : E n :=
  (inner ℝ y e)⁻¹ • (y + (1 - inner ℝ y e) • e)

theorem proj_lip {n : ℕ} {e : E n} (he : ‖e‖ = 1) {R : ℝ} {y y' : E n}
    (hy1 : 1 ≤ inner ℝ y e) (hy1' : 1 ≤ inner ℝ y' e) (hyR : ‖y‖ ≤ R) :
    ‖proj e y - proj e y'‖ ≤ (2 * R + 3) * ‖y - y'‖ := by
  set a := inner ℝ y e with ha_def
  set b := inner ℝ y' e with hb_def
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have key : proj e y - proj e y' =
      (a⁻¹ - b⁻¹) • (y - a • e + e) + b⁻¹ • ((y - a • e) - (y' - b • e)) := by
    unfold proj
    rw [← ha_def, ← hb_def]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hab : |a - b| ≤ ‖y - y'‖ := by
    have : a - b = inner ℝ (y - y') e := by rw [inner_sub_left]
    rw [this]
    calc _ ≤ ‖y - y'‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [he, mul_one]
  have ha : |a| ≤ ‖y‖ := by
    have := abs_real_inner_le_norm y e
    rwa [he, mul_one] at this
  have h1 : |a⁻¹ - b⁻¹| ≤ ‖y - y'‖ := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (by positivity : 0 < a * b),
      div_le_iff₀ (by positivity)]
    rw [abs_sub_comm] at hab
    have hab1 : 1 ≤ a * b := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hab1 (norm_nonneg (y - y'))]
  have h2 : ‖y - a • e + e‖ ≤ 2 * R + 1 := by
    calc _ ≤ ‖y - a • e‖ + ‖e‖ := norm_add_le _ _
      _ ≤ ‖y‖ + ‖a • e‖ + ‖e‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖y‖ + |a| + 1 := by rw [norm_smul, he, Real.norm_eq_abs, mul_one]
      _ ≤ 2 * R + 1 := by linarith
  have h3 : ‖(y - a • e) - (y' - b • e)‖ ≤ 2 * ‖y - y'‖ := by
    have : (y - a • e) - (y' - b • e) = (y - y') - (a - b) • e := by module
    rw [this]
    calc _ ≤ ‖y - y'‖ + ‖(a - b) • e‖ := norm_sub_le _ _
      _ = ‖y - y'‖ + |a - b| := by rw [norm_smul, he, Real.norm_eq_abs, mul_one]
      _ ≤ _ := by linarith
  have h4 : |b⁻¹| ≤ 1 := by
    rw [abs_of_pos (by positivity)]; exact inv_le_one_of_one_le₀ hy1'
  rw [key]
  calc _ ≤ ‖(a⁻¹ - b⁻¹) • (y - a • e + e)‖ + ‖b⁻¹ • ((y - a • e) - (y' - b • e))‖ :=
        norm_add_le _ _
    _ = |a⁻¹ - b⁻¹| * ‖y - a • e + e‖ + |b⁻¹| * ‖(y - a • e) - (y' - b • e)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖y - y'‖ * (2 * R + 1) + 1 * (2 * ‖y - y'‖) := by gcongr
    _ = _ := by ring

/-- The chart: translate by `(ρ+1) e`, apply the projective map, dilate by `t`. -/
noncomputable def chart {n : ℕ} (e : E n) (ρ t : ℝ) (x : E n) : E n :=
  t • proj e (x + (ρ + 1) • e)

theorem inner_shift {n : ℕ} {e : E n} (he : ‖e‖ = 1) (x : E n) (ρ : ℝ) :
    inner ℝ (x + (ρ + 1) • e) e = inner ℝ x e + (ρ + 1) := by
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring

theorem chart_lip {n : ℕ} {e : E n} (he : ‖e‖ = 1) {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    {x x' : E n} (hx : ‖x‖ ≤ ρ) (hx' : ‖x'‖ ≤ ρ) :
    dist (chart e ρ t x) (chart e ρ t x') ≤ t * (4 * ρ + 5) * dist x x' := by
  have hlow : ∀ x : E n, ‖x‖ ≤ ρ → 1 ≤ inner ℝ (x + (ρ + 1) • e) e := by
    intro x hx
    rw [inner_shift he]
    have := abs_real_inner_le_norm x e
    rw [he, mul_one] at this
    linarith [neg_abs_le (inner ℝ x e)]
  have hR : ‖x + (ρ + 1) • e‖ ≤ 2 * ρ + 1 := by
    calc _ ≤ ‖x‖ + ‖(ρ + 1) • e‖ := norm_add_le _ _
      _ = ‖x‖ + (ρ + 1) := by rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ _ := by linarith
  have := proj_lip he (hlow x hx) (hlow x' hx') hR
  have hsub : x + (ρ + 1) • e - (x' + (ρ + 1) • e) = x - x' := by abel
  rw [hsub] at this
  unfold chart
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  calc _ ≤ t * ((2 * (2 * ρ + 1) + 3) * ‖x - x'‖) := mul_le_mul_of_nonneg_left this ht
    _ = _ := by ring

theorem chart_segment {n : ℕ} (hn1 : 1 ≤ n) {S : Set (E n)} (hN : IsNikodymSet S) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hSρ : ∀ x ∈ S, ‖x‖ ≤ ρ) {e u : E n} (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (hue : 1 / (n : ℝ) ≤ |inner ℝ u e|) :
    ∃ b, affineSegment ℝ b (b + u) ⊆ chart e ρ ((2 * ρ + 1) ^ 2 * (2 * ρ + n + 2)) '' S := by
  set t := (2 * ρ + 1) ^ 2 * (2 * ρ + n + 2) with ht_def
  clear_value t
  set α := inner ℝ u e with hα_def
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hα0 : 0 < |α| := lt_of_lt_of_le (by positivity) hue
  have hαne : α ≠ 0 := abs_pos.1 hα0
  have hα1 : |α| ≤ 1 := by
    have := abs_real_inner_le_norm u e
    rwa [hu, he, mul_one] at this
  set z : E n := α⁻¹ • u - e with hz_def
  have hze : inner ℝ z e = 0 := by
    rw [hz_def, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, ← hα_def,
      inv_mul_cancel₀ hαne]; ring
  have hz : ‖z‖ ≤ n + 1 := by
    calc ‖z‖ ≤ ‖α⁻¹ • u‖ + ‖e‖ := norm_sub_le _ _
      _ = |α|⁻¹ + 1 := by rw [norm_smul, hu, he, mul_one, norm_inv, Real.norm_eq_abs]
      _ ≤ n + 1 := by
        have : |α|⁻¹ ≤ n := by
          rw [inv_le_comm₀ hα0 hn0]; rwa [one_div] at hue
        linarith
  obtain ⟨v, hv, s, hseg⟩ := hN (z - (ρ + 1) • e)
  set a := inner ℝ v e with ha_def
  set x : ℝ → E n := fun σ => z - (ρ + 1) • e + σ • v with hx_def
  have hmem : ∀ σ ∈ Set.Icc s (s + 1), x σ ∈ S := by
    intro σ hσ
    apply hseg
    rw [segment_eq_image']
    exact ⟨σ - s, ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, by simp only [hx_def]; module⟩
  have hxe : ∀ σ, inner ℝ (x σ) e = -(ρ + 1) + σ * a := by
    intro σ
    simp only [hx_def]
    rw [inner_add_left, inner_sub_left, hze, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he, ← ha_def]; ring
  have hlam : ∀ σ ∈ Set.Icc s (s + 1), 1 ≤ σ * a ∧ σ * a ≤ 2 * ρ + 1 := by
    intro σ hσ
    have h1 := hSρ _ (hmem σ hσ)
    have h2 := abs_real_inner_le_norm (x σ) e
    rw [he, mul_one, hxe] at h2
    constructor
    · linarith [neg_abs_le (-(ρ + 1) + σ * a)]
    · linarith [le_abs_self (-(ρ + 1) + σ * a)]
  have hsig : ∀ σ ∈ Set.Icc s (s + 1), |σ| ≤ 2 * ρ + n + 2 := by
    intro σ hσ
    have h1 := hSρ _ (hmem σ hσ)
    have : σ • v = x σ - z + (ρ + 1) • e := by simp only [hx_def]; abel
    have h2 : ‖σ • v‖ = |σ| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
    rw [← h2, this]
    calc _ ≤ ‖x σ - z‖ + ‖(ρ + 1) • e‖ := norm_add_le _ _
      _ ≤ ‖x σ‖ + ‖z‖ + ‖(ρ + 1) • e‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖x σ‖ + ‖z‖ + (ρ + 1) := by
        rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ _ := by linarith
  have hs : s ∈ Set.Icc s (s + 1) := ⟨le_rfl, by linarith⟩
  have hs1 : s + 1 ∈ Set.Icc s (s + 1) := ⟨by linarith, le_rfl⟩
  have hsa := hlam s hs
  have hs1a := hlam (s + 1) hs1
  have hne : ∀ σ ∈ Set.Icc s (s + 1), σ ≠ 0 ∧ a ≠ 0 := by
    intro σ hσ
    have := (hlam σ hσ).1
    constructor <;> intro h <;> rw [h] at this <;> simp at this <;> linarith
  have ha0 : a ≠ 0 := (hne s hs).2
  -- the value of the chart along the segment
  set g : ℝ → ℝ := fun σ => t / (σ * a * α) with hg_def
  set W : E n := t • (a⁻¹ • v - e) with hW_def
  have hval : ∀ σ ∈ Set.Icc s (s + 1), chart e ρ t (x σ) = W + g σ • u := by
    intro σ hσ
    obtain ⟨hσ0, -⟩ := hne σ hσ
    have hin : inner ℝ (x σ + (ρ + 1) • e) e = σ * a := by rw [inner_shift he, hxe]; ring
    unfold chart proj
    rw [hin]
    have hxs : x σ + (ρ + 1) • e = α⁻¹ • u - e + σ • v := by simp only [hx_def, hz_def]; abel
    rw [hxs]
    simp only [hW_def, hg_def]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hcont : ContinuousOn g (Set.uIcc s (s + 1)) := by
    rw [Set.uIcc_of_le (by linarith)]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro σ hσ
    obtain ⟨h1, h2⟩ := hne σ hσ
    exact mul_ne_zero (mul_ne_zero h1 h2) hαne
  have hivt := intermediate_value_uIcc hcont
  -- the gap
  have hgap : 1 ≤ |g s - g (s + 1)| := by
    have hs0 := (hne s hs).1
    have hs10 := (hne (s + 1) hs1).1
    have e1 : g s - g (s + 1) = t * a / (α * (s * a) * ((s + 1) * a)) := by
      simp only [hg_def]; field_simp; ring
    have hpos : 0 < (s * a) * ((s + 1) * a) := by nlinarith
    have htpos : 0 < t := by rw [ht_def]; positivity
    have hD : |α * (s * a) * ((s + 1) * a)| = |α| * ((s * a) * ((s + 1) * a)) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < s * a),
        abs_of_pos (by linarith : 0 < (s + 1) * a)]; ring
    rw [e1, abs_div, abs_mul t a, abs_of_pos htpos, hD, le_div_iff₀ (by positivity)]
    have hsabs := hsig s hs
    have haa : 1 ≤ |s| * |a| := by
      rw [← abs_mul]; exact le_trans hsa.1 (le_abs_self _)
    have hta : (2 * ρ + 1) ^ 2 ≤ t * |a| := by
      rw [ht_def]
      have : 1 ≤ (2 * ρ + n + 2) * |a| := le_trans haa (by gcongr)
      nlinarith [sq_nonneg (2 * ρ + 1)]
    have hprod : (s * a) * ((s + 1) * a) ≤ (2 * ρ + 1) ^ 2 := by
      nlinarith
    calc 1 * (|α| * ((s * a) * ((s + 1) * a))) ≤ 1 * ((s * a) * ((s + 1) * a)) := by
          nlinarith
      _ ≤ (2 * ρ + 1) ^ 2 := by linarith
      _ ≤ t * |a| := hta
  set m := min (g s) (g (s + 1)) with hm_def
  refine ⟨W + m • u, ?_⟩
  rw [affineSegment_eq_segment, segment_eq_image']
  rintro _ ⟨θ, hθ, rfl⟩
  have hmem' : m + θ ∈ Set.uIcc (g s) (g (s + 1)) := by
    rw [Set.mem_uIcc]
    rcases le_total (g s) (g (s + 1)) with h | h
    · left
      have hm : m = g s := min_eq_left h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hgap
      constructor <;> linarith [hθ.1, hθ.2]
    · right
      have hm : m = g (s + 1) := min_eq_right h
      rw [abs_of_nonneg (by linarith)] at hgap
      constructor <;> linarith [hθ.1, hθ.2]
  obtain ⟨σ, hσ, hgσ⟩ := hivt hmem'
  rw [Set.uIcc_of_le (by linarith)] at hσ
  refine ⟨x σ, hmem σ hσ, ?_⟩
  rw [hval σ hσ, hgσ]
  module

theorem exists_large_coord {n : ℕ} (hn1 : 1 ≤ n) {u : E n} (hu : ‖u‖ = 1) :
    ∃ i : Fin n, 1 / (n : ℝ) ≤ |u i| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsum : ∑ i, (u i) ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hu]; norm_num
  by_contra h
  push Not at h
  have hsq : ∀ i, (u i) ^ 2 < 1 / n := by
    intro i
    have h1 := h i
    have h2 : |u i| ^ 2 = (u i) ^ 2 := sq_abs _
    have h3 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn1
    nlinarith [abs_nonneg (u i)]
  have : ∑ i : Fin n, (u i) ^ 2 < ∑ _i : Fin n, 1 / (n : ℝ) :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun i _ => hsq i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [mul_one_div_cancel hn0.ne'] at this
  linarith

end NK

open NK in
theorem nikodymSetConjecture_of_kakeyaSetConjecture_dev (n : ℕ) (hn : 2 ≤ n) :
    KakeyaSetConjecture n → NikodymSetConjecture n := by
  intro hKak S hSb hN
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ρ0, hρ0⟩ := hSb.subset_closedBall (0 : E n)
  set ρ := max ρ0 0 with hρ_def
  have hρ : 0 ≤ ρ := le_max_right _ _
  have hSρ : ∀ x ∈ S, ‖x‖ ≤ ρ := by
    intro x hx
    have := hρ0 hx
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set t : ℝ := (2 * ρ + 1) ^ 2 * (2 * ρ + n + 2) with ht_def
  have ht1 : 1 ≤ t := by
    rw [ht_def]
    have h1 : 1 ≤ (2 * ρ + 1) ^ 2 := by nlinarith
    have h2 : 1 ≤ 2 * ρ + n + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  set ψ : Fin n → E n → E n := fun i => chart (EuclideanSpace.single i 1) ρ t with hψ_def
  set L : ℝ := t * (4 * ρ + 5) with hL_def
  have hL1 : 1 ≤ L := by rw [hL_def]; nlinarith
  have hlip : ∀ i, ∀ x ∈ S, ∀ y ∈ S, dist (ψ i x) (ψ i y) ≤ L * dist x y := by
    intro i x hx y hy
    exact chart_lip (by simp) hρ (by linarith) (hSρ x hx) (hSρ y hy)
  set K := ⋃ i, ψ i '' S with hK_def
  have hKb : Bornology.IsBounded K :=
    Bornology.isBounded_iUnion.2 fun i => isBounded_image_of_lip hSb _ (by linarith) (hlip i)
  have hKk : FCP.Kakeya.IsKakeya K := by
    intro u hu
    obtain ⟨i, hi⟩ := exists_large_coord hn1 hu
    have hin : inner ℝ u (EuclideanSpace.single i (1 : ℝ)) = u i := by
      rw [EuclideanSpace.inner_single_right]; simp
    obtain ⟨b, hb⟩ := chart_segment hn1 hN hρ hSρ (e := EuclideanSpace.single i (1 : ℝ))
      (by simp) hu (by rw [hin]; exact hi)
    exact ⟨b, hb.trans (Set.subset_iUnion (fun i => ψ i '' S) i)⟩
  set B : Set (E n) := closedBall 0 (ρ + 1) with hB_def
  have hBb : Bornology.IsBounded B := isBounded_closedBall
  have hBk : FCP.Kakeya.IsKakeya B := by
    intro v hv
    refine ⟨0, ?_⟩
    rw [affineSegment_eq_segment]
    apply (convex_closedBall (0 : E n) (ρ + 1)).segment_subset
    · simp; linarith
    · simp [hv]; linarith
  have hSB : S ⊆ B := by
    intro x hx
    rw [hB_def, mem_closedBall, dist_zero_right]
    linarith [hSρ x hx]
  have hSne : S.Nonempty := by
    obtain ⟨v, -, s, hs⟩ := hN 0
    exact ⟨_, hs (left_mem_segment ℝ _ _)⟩
  have hKne : K.Nonempty := by
    have hu : ‖EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)‖ = 1 := by simp
    obtain ⟨b, hb⟩ := hKk _ hu
    exact ⟨b, hb (left_mem_affineSegment ℝ _ _)⟩
  have hnR : (n : ℝ) ≠ 0 := by positivity
  apply dims_eq hnR hSb hSne hKb hKne hBb hSB (hKak K hKb hKk) (hKak B hBb hBk)
    (c := 2 * L) (by linarith) (M := n) hn1
  intro r hr
  calc coveringNumber K (2 * L * r) ≤ ∑ i, coveringNumber (ψ i '' S) (2 * L * r) :=
        cn_iUnion_le _ (fun i => isBounded_image_of_lip hSb _ (by linarith) (hlip i))
          (by positivity)
    _ ≤ ∑ _i : Fin n, coveringNumber S r :=
        Finset.sum_le_sum fun i _ => cn_image_le hSb (ψ i) (by linarith) (hlip i) hr
    _ = n * coveringNumber S r := by simp

end TaoBR

open TaoBR in
theorem solution (n : ℕ) (hn : 2 ≤ n) : KakeyaSetConjecture n → NikodymSetConjecture n :=
  nikodymSetConjecture_of_kakeyaSetConjecture_dev n hn
