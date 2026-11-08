-- Prove2me | solution 1 for ProjSchedTW.StableSchedules.stable_classes_extreme_points
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:22:35.351511+00:00
-- url     : https://prove2.me/submissions/53664fa5-f197-40e5-adee-07b367878c55

import Mathlib
import Definitions.Def_ProjSchedTW_StableSchedules_Project
import Definitions.Def_ProjSchedTW_StableSchedules_Shifts

open ProjSchedTW.StableSchedules Filter Topology

namespace Stable6Aux

variable {n : ℕ} {K : Type}

lemma mem_active {P : Project n K} {Z : Fin (n + 2) → ℝ} {t : ℝ} {i : Fin (n + 2)} :
    i ∈ activeSet P Z t ↔ Z i ≤ t ∧ t < Z i + (P.p i : ℝ) := by
  classical
  unfold activeSet
  simp

lemma active_pos {P : Project n K} {Z : Fin (n + 2) → ℝ} {t : ℝ} {i : Fin (n + 2)}
    (h : i ∈ activeSet P Z t) : 0 < (P.p i : ℝ) := by
  rw [mem_active] at h; linarith [h.1, h.2]

lemma active_unordered {P : Project n K} {Z : Fin (n + 2) → ℝ} {t : ℝ} {i j : Fin (n + 2)}
    (hi : i ∈ activeSet P Z t) (hj : j ∈ activeSet P Z t) : ¬ (Z i + (P.p i : ℝ) ≤ Z j) := by
  rw [mem_active] at hi hj; intro h; linarith [hi.2, hj.1]

lemma common_time (P : Project n K) (Y : Fin (n + 2) → ℝ) (hY : ∀ i, 0 ≤ Y i)
    (A : Finset (Fin (n + 2))) (hp : ∀ i ∈ A, 0 < (P.p i : ℝ))
    (h : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ (Y i + (P.p i : ℝ) ≤ Y j)) :
    ∃ t, 0 ≤ t ∧ A ⊆ activeSet P Y t := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · exact ⟨0, le_refl _, by simp [hA]⟩
  obtain ⟨i, hiA, hi⟩ := Finset.exists_max_image A Y hA
  refine ⟨Y i, hY i, ?_⟩
  intro j hj
  rw [mem_active]
  refine ⟨hi j hj, ?_⟩
  by_cases hij : j = i
  · subst hij; linarith [hp j hj]
  · have := h j hj i hiA hij
    linarith [not_le.mp this]

lemma resFeas_of {P : Project n K} {Z : Fin (n + 2) → ℝ} (hZ0 : Z 0 = 0) (hZ : ∀ i, 0 ≤ Z i)
    (H : ∀ t : ℝ, 0 ≤ t → ∃ Y ∈ resourceFeasibleSet P,
      ∀ i ∈ activeSet P Z t, ∀ j ∈ activeSet P Z t, i ≠ j → ¬ (Y i + (P.p i : ℝ) ≤ Y j)) :
    Z ∈ resourceFeasibleSet P := by
  refine ⟨hZ0, hZ, ?_⟩
  intro k t ht
  obtain ⟨Y, hY, hYA⟩ := H t ht
  obtain ⟨t', ht', hsub⟩ := common_time P Y hY.2.1 (activeSet P Z t)
    (fun i hi => active_pos hi) hYA
  have h1 : usage P Z k t ≤ usage P Y k t' := by
    unfold usage
    exact Finset.sum_le_sum_of_subset hsub
  exact h1.trans (hY.2.2 k t' ht')

lemma resFeas_mono {P : Project n K} {Y Z : Fin (n + 2) → ℝ} (hY : Y ∈ resourceFeasibleSet P)
    (hZ0 : Z 0 = 0) (hZ : ∀ i, 0 ≤ Z i) (hO : scheduleOrder P Y ⊆ scheduleOrder P Z) :
    Z ∈ resourceFeasibleSet P := by
  refine resFeas_of hZ0 hZ (fun t _ => ⟨Y, hY, ?_⟩)
  intro i hi j hj hij hle
  have : (i, j) ∈ scheduleOrder P Z := hO ⟨hij, hle⟩
  exact active_unordered hi hj this.2

lemma feas_mono {P : Project n K} {Y Z : Fin (n + 2) → ℝ} (hY : Y ∈ feasibleSet P)
    (hZ : Z ∈ timeFeasibleSet P) (hO : scheduleOrder P Y ⊆ scheduleOrder P Z) :
    Z ∈ feasibleSet P :=
  ⟨hZ, resFeas_mono hY.2 hZ.1 hZ.2.1 hO⟩

lemma convex_time (P : Project n K) : Convex ℝ (timeFeasibleSet P) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · simp [hx.1, hy.1]
  · intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.2.1 i, hy.2.1 i]
  · intro e he
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hx.2.2 e he; have h2 := hy.2.2 e he
    have hd : (P.δ e.1 e.2 : ℝ) = a * P.δ e.1 e.2 + b * P.δ e.1 e.2 := by
      rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma convex_orderPolytope (P : Project n K) (O : Set (Fin (n + 2) × Fin (n + 2))) :
    Convex ℝ (orderPolytope P O) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_time P hx.1 hy.1 ha hb hab, ?_⟩
  intro e he
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := hx.2 e he; have h2 := hy.2 e he
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- Generic: extreme points via opposite pairs. -/
lemma ext_iff (M : Set (Fin (n + 2) → ℝ)) {S : Fin (n + 2) → ℝ} (hS : S ∈ M) :
    S ∈ M.extremePoints ℝ ↔ ¬ ∃ S' S'', S' ∈ M ∧ S'' ∈ M ∧ AreOpposite S S' S'' := by
  rw [mem_extremePoints]
  constructor
  · rintro ⟨-, h⟩ ⟨S', S'', h1, h2, hne, -, lam, hlam, heq⟩
    apply hne
    refine (h S' h1 S'' h2 ⟨-lam / (1 - lam), 1 / (1 - lam), ?_, ?_, ?_, ?_⟩).1
    · apply div_pos <;> linarith
    · apply div_pos <;> linarith
    · have h1l : (1 - lam) ≠ 0 := by linarith
      rw [← add_div, div_eq_one_iff_eq h1l]; ring
    · funext i
      have := congrFun heq i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1l : (1 - lam) ≠ 0 := by linarith
      field_simp
      rw [show S'' i = S i + lam * (S' i - S i) by linarith]
      ring
  · rintro h
    refine ⟨hS, ?_⟩
    rintro x1 hx1 x2 hx2 ⟨a, b, ha, hb, hab, hS'⟩
    have key : ∀ i, b * (x2 i - S i) = -a * (x1 i - S i) := by
      intro i
      have := congrFun hS' i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith
    by_cases h1 : x1 = S
    · refine ⟨h1, ?_⟩
      funext i
      have := key i
      rw [h1] at this
      simp at this
      rcases this with h | h
      · linarith
      · linarith
    · exfalso
      apply h
      refine ⟨x1, x2, hx1, hx2, h1, ?_, -a / b, ?_, ?_⟩
      · intro h2
        apply h1
        funext i
        have := key i
        rw [h2] at this
        simp at this
        rcases this with h | h
        · linarith
        · linarith
      · apply div_neg_of_neg_of_pos <;> linarith
      · funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have := key i
        field_simp
        linarith

lemma uniform_iff {M : Set (Fin (n + 2) → ℝ)} {S : Fin (n + 2) → ℝ} (A : Prop) (hA : A)
    (hS : S ∈ M) (Sh : (Fin (n + 2) → ℝ) → Prop) (hSh : ∀ S', Sh S' ↔ S' ∈ M ∧ S' ≠ S) :
    (A ∧ ¬ ∃ S' S'', Sh S' ∧ Sh S'' ∧ AreOpposite S S' S'') ↔ S ∈ M.extremePoints ℝ := by
  rw [ext_iff M hS]
  simp only [hSh]
  constructor
  · rintro ⟨-, h⟩ ⟨S', S'', h1, h2, h3⟩
    exact h ⟨S', S'', ⟨h1, h3.1⟩, ⟨h2, h3.2.1⟩, h3⟩
  · intro h
    refine ⟨hA, ?_⟩
    rintro ⟨S', S'', h1, h2, h3⟩
    exact h ⟨S', S'', h1.1, h2.1, h3⟩


lemma local_star (P : Project n K) (x : Fin (n + 2) → ℝ) (hx : x ∈ feasibleSet P) :
    ∀ᶠ y in 𝓝 x, y ∈ feasibleSet P → JoinedIn (feasibleSet P) x y := by
  have hev : ∀ᶠ y in 𝓝 x, ∀ i j : Fin (n + 2), x j < x i + (P.p i : ℝ) →
      y j < y i + (P.p i : ℝ) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h : x j < x i + (P.p i : ℝ)
    · have := ContinuousAt.eventually_lt (f := fun y : Fin (n + 2) → ℝ => y j)
        (g := fun y : Fin (n + 2) → ℝ => y i + (P.p i : ℝ)) (x₀ := x)
        (continuous_apply j).continuousAt
        ((continuous_apply i).add continuous_const).continuousAt h
      filter_upwards [this] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun y h' => absurd h' h
  filter_upwards [hev] with y hy hyF
  apply JoinedIn.of_segment_subset
  intro z hz
  have hzT : z ∈ timeFeasibleSet P := (convex_time P).segment_subset hx.1 hyF.1 hz
  refine feas_mono hyF hzT ?_
  rintro ⟨i, j⟩ ⟨hij, hle⟩
  refine ⟨hij, ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  have hxle : x i + (P.p i : ℝ) ≤ x j := by
    by_contra hc
    exact absurd hle (not_le.mpr (hy i j (not_le.mp hc)))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hd : (P.p i : ℝ) = a * P.p i + b * P.p i := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hxle ha, mul_le_mul_of_nonneg_left hle hb]

lemma comp_joined (P : Project n K) {S y : Fin (n + 2) → ℝ} (hS : S ∈ feasibleSet P)
    (hy : y ∈ connectedComponentIn (feasibleSet P) S) : JoinedIn (feasibleSet P) S y := by
  set F := feasibleSet P
  let Q : Set F := {w | JoinedIn F S w}
  have hnhd : ∀ w : F, ∃ u ∈ 𝓝 (w : Fin (n + 2) → ℝ), ∀ v : F, (v : Fin (n + 2) → ℝ) ∈ u →
      JoinedIn F w v := by
    intro w
    refine ⟨_, local_star P w w.2, fun v hv => hv v.2⟩
  have hopen : IsOpen Q := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    obtain ⟨u, hu, huv⟩ := hnhd w
    rw [mem_nhds_subtype]
    exact ⟨u, hu, fun v hv => JoinedIn.trans hw (huv v hv)⟩
  have hclosed : IsClosed Q := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro w hw
    obtain ⟨u, hu, huv⟩ := hnhd w
    rw [mem_nhds_subtype]
    exact ⟨u, hu, fun v hv hvQ => hw (JoinedIn.trans hvQ (huv v hv).symm)⟩
  have hsub := (IsClopen.connectedComponent_subset (x := (⟨S, hS⟩ : F)) ⟨hclosed, hopen⟩
    (JoinedIn.refl hS))
  rw [connectedComponentIn_eq_image hS] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hsub hw

lemma small_order (P : Project n K) (S v : Fin (n + 2) → ℝ) :
    ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ i j : Fin (n + 2), S j < S i + (P.p i : ℝ) →
      S j + η * v j < S i + η * v i + (P.p i : ℝ) := by
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  by_cases h : S j < S i + (P.p i : ℝ)
  · have := ContinuousAt.eventually_lt (f := fun η : ℝ => S j + η * v j)
        (g := fun η : ℝ => S i + η * v i + (P.p i : ℝ)) (x₀ := 0)
        (by fun_prop) (by fun_prop) (by simpa using h)
    filter_upwards [this] with y hy _ using hy
  · exact Filter.Eventually.of_forall fun y h' => absurd h' h

lemma seg_feas (P : Project n K) {S S' : Fin (n + 2) → ℝ} (hS : S ∈ feasibleSet P)
    (hS' : S' ∈ feasibleSet P)
    (hO : scheduleOrder P S ⊆ scheduleOrder P S' ∨ scheduleOrder P S' ⊆ scheduleOrder P S) :
    segment ℝ S S' ⊆ feasibleSet P := by
  intro z hz
  have hzT : z ∈ timeFeasibleSet P := (convex_time P).segment_subset hS.1 hS'.1 hz
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  have comb : ∀ i j : Fin (n + 2), S i + (P.p i : ℝ) ≤ S j → S' i + (P.p i : ℝ) ≤ S' j →
      (a • S + b • S') i + (P.p i : ℝ) ≤ (a • S + b • S') j := by
    intro i j h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hd : (P.p i : ℝ) = a * P.p i + b * P.p i := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  rcases hO with hO | hO
  · refine feas_mono hS hzT ?_
    rintro ⟨i, j⟩ he
    exact ⟨he.1, comb i j he.2 (hO he).2⟩
  · refine feas_mono hS' hzT ?_
    rintro ⟨i, j⟩ he
    exact ⟨he.1, comb i j (hO he).2 he.2⟩


lemma ev_small (c : ℝ) : ∀ᶠ η in 𝓝[>] (0:ℝ), 0 < c → η < c := by
  by_cases hc : 0 < c
  · exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hc)).mono
      fun η h _ => h
  · exact Filter.Eventually.of_forall fun η h => absurd h hc

lemma zz {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hab : a ≤ b) (hne : a ≠ b) :
    a = 0 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at *

lemma core (P : Project n K) {S d : Fin (n + 2) → ℝ} (hS : S ∈ feasibleSet P)
    (m : Fin (n + 2)) (hm : ∀ i, d i ≤ d m) (hdm : 0 < d m)
    (h : ∀ᶠ η in 𝓝[>] (0:ℝ), S + η • d ∈ feasibleSet P ∧ S - η • d ∈ feasibleSet P) :
    ∃ O, IsFeasibleOrder P O ∧ O ⊆ scheduleOrder P S ∧
      S ∉ (orderPolytope P O).extremePoints ℝ := by
  classical
  set z : Fin (n + 2) → ℝ := fun i => if d i = d m then 1 else 0 with hzdef
  have hz01 : ∀ i, z i = 0 ∨ z i = 1 := by
    intro i; simp only [hzdef]; split_ifs <;> simp
  have hzmono : ∀ i j, d i ≤ d j → z i ≤ z j := by
    intro i j hij
    simp only [hzdef]
    split_ifs with h1 h2 <;> try norm_num
    exact h2 (le_antisymm (hm j) (h1 ▸ hij))
  have hz0 : ∀ i, d i = 0 → z i = 0 := by
    intro i hi; simp only [hzdef]; rw [if_neg]; linarith
  have hzm : z m = 1 := by simp [hzdef]
  set O : Set (Fin (n + 2) × Fin (n + 2)) := {e | e.1 ≠ e.2 ∧ 0 < (P.p e.1 : ℝ) ∧
    0 < (P.p e.2 : ℝ) ∧ S e.1 + (P.p e.1 : ℝ) ≤ S e.2 ∧
    (S e.1 + (P.p e.1 : ℝ) < S e.2 ∨ z e.1 = z e.2)} with hOdef
  have hev := ((((h.and (small_order P S d)).and (small_order P S (-d))).and
    (Filter.eventually_all.2 fun i => ev_small (S i))).and
    ((Filter.eventually_all.2 fun e : Fin (n + 2) × Fin (n + 2) =>
      ev_small (S e.2 - S e.1 - (P.δ e.1 e.2 : ℝ))).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_small (S j - S i - (P.p i : ℝ))))).and self_mem_nhdsWithin
  obtain ⟨η, ⟨⟨⟨⟨⟨hFp, hFm⟩, hordp⟩, hordm⟩, hsl1⟩, hsl2, hsl3⟩, hη⟩ := hev.exists
  have hη0 : (0:ℝ) < η := hη
  simp only [Pi.neg_apply, mul_neg] at hordm
  have hYp : ∀ i, (S + η • d) i = S i + η * d i := fun i => by simp
  have hYm : ∀ i, (S - η • d) i = S i - η * d i := fun i => by simp
  have hzb : ∀ i, 0 ≤ η * z i ∧ η * z i ≤ η := by
    intro i; rcases hz01 i with h | h <;> rw [h] <;> constructor <;> linarith
  -- strict order
  have hstrict : ProjSchedTW.ActiveSchedules.IsStrictOrderRel O := by
    constructor
    · rintro i j ⟨-, hpi, hpj, h1, -⟩ ⟨-, -, -, h2, -⟩
      simp only at h1 h2
      linarith
    · rintro i j l ⟨-, hpi, hpj, h1, -⟩ ⟨-, -, hpl, h2, -⟩
      simp only at h1 h2 hpi hpj hpl
      refine ⟨?_, hpi, hpl, by simp only; linarith, Or.inl (by simp only; linarith)⟩
      simp only
      intro hc; rw [hc] at h1; linarith
  have hOS : O ⊆ scheduleOrder P S := fun e he => ⟨he.1, he.2.2.2.1⟩
  have hSO : S ∈ orderPolytope P O := ⟨hS.1, fun e he => he.2.2.2.1⟩
  -- feasibility of the order polytope
  have hsubF : orderPolytope P O ⊆ feasibleSet P := by
    intro Z hZ
    refine ⟨hZ.1, resFeas_of hZ.1.1 hZ.1.2.1 ?_⟩
    intro t _
    have hnotO : ∀ a ∈ activeSet P Z t, ∀ b ∈ activeSet P Z t, (a, b) ∉ O :=
      fun a ha b hb hab => active_unordered ha hb (hZ.2 _ hab)
    by_cases h1 : ∀ i ∈ activeSet P Z t, ∀ j ∈ activeSet P Z t, i ≠ j →
        ¬ ((S + η • d) i + (P.p i : ℝ) ≤ (S + η • d) j)
    · exact ⟨_, hFp.2, h1⟩
    by_cases h2 : ∀ i ∈ activeSet P Z t, ∀ j ∈ activeSet P Z t, i ≠ j →
        ¬ ((S - η • d) i + (P.p i : ℝ) ≤ (S - η • d) j)
    · exact ⟨_, hFm.2, h2⟩
    exfalso
    push_neg at h1 h2
    obtain ⟨i, hi, j, hj, hij, hle⟩ := h1
    obtain ⟨k, hk, l, hl, hkl, hle2⟩ := h2
    rw [hYp, hYp] at hle
    rw [hYm, hYm] at hle2
    have hpi := active_pos hi; have hpj := active_pos hj
    have hpk := active_pos hk; have hpl := active_pos hl
    have hSij : S i + (P.p i : ℝ) ≤ S j := by
      by_contra c; have := hordp i j (not_le.mp c); linarith
    have hSkl : S k + (P.p k : ℝ) ≤ S l := by
      by_contra c; have := hordm k l (not_le.mp c); linarith
    have hn1 : ¬ (S i + (P.p i : ℝ) < S j ∨ z i = z j) := fun hc =>
      hnotO i hi j hj ⟨hij, hpi, hpj, hSij, hc⟩
    have hn2 : ¬ (S k + (P.p k : ℝ) < S l ∨ z k = z l) := fun hc =>
      hnotO k hk l hl ⟨hkl, hpk, hpl, hSkl, hc⟩
    push_neg at hn1 hn2
    have eij : S i + (P.p i : ℝ) = S j := le_antisymm hSij hn1.1
    have ekl : S k + (P.p k : ℝ) = S l := le_antisymm hSkl hn2.1
    have dij : d i ≤ d j := by
      by_contra c; push_neg at c; nlinarith
    have dlk : d l ≤ d k := by
      by_contra c; push_neg at c; nlinarith
    have zij := hzmono i j dij
    have zlk := hzmono l k dlk
    obtain ⟨zi, zj⟩ := zz (hz01 i) (hz01 j) zij hn1.2
    obtain ⟨zl, zk⟩ := zz (hz01 l) (hz01 k) zlk (Ne.symm hn2.2)
    by_cases hkj : S k + (P.p k : ℝ) ≤ S j
    · have hkj' : k ≠ j := by rintro rfl; linarith
      exact hnotO k hk j hj ⟨hkj', hpk, hpj, hkj, Or.inr (by rw [zk, zj])⟩
    · push_neg at hkj
      have hil : i ≠ l := by intro hc; rw [hc] at eij; linarith
      exact hnotO i hi l hl ⟨hil, hpi, hpl, by linarith, Or.inl (by linarith)⟩
  refine ⟨O, ⟨hstrict, ⟨S, hSO⟩, hsubF⟩, hOS, ?_⟩
  -- non-extremality
  have hd0 : d 0 = 0 := by
    have h1 := hFp.1.1; rw [hYp, hS.1.1] at h1
    rcases mul_eq_zero.mp (by linarith : η * d 0 = 0) with h | h
    · linarith
    · exact h
  have hzeqd : ∀ i j, d i = d j → η * z i = η * z j := by
    intro i j hij; rw [le_antisymm (hzmono i j hij.le) (hzmono j i hij.ge)]
  have hmem : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → S + (σ * η) • z ∈ orderPolytope P O := by
    intro σ hσ
    have hval : ∀ i, (S + (σ * η) • z) i = S i + σ * (η * z i) := fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hval, hS.1.1, hz0 0 hd0]; simp
    · intro i
      rw [hval]
      by_cases hSi : 0 < S i
      · have := hsl1 i hSi
        rcases hσ with rfl | rfl <;> linarith [hzb i]
      · have hSi0 : S i = 0 := le_antisymm (not_lt.mp hSi) (hS.1.2.1 i)
        have h1 := hFp.1.2.1 i; have h2 := hFm.1.2.1 i
        rw [hYp] at h1; rw [hYm] at h2
        have hdi : d i = 0 := by
          rw [hSi0] at h1 h2
          have a1 : 0 ≤ d i := by nlinarith
          have a2 : d i ≤ 0 := by nlinarith
          linarith
        rw [hz0 i hdi, hSi0]; simp
    · intro e he
      rw [hval, hval]
      have h0 := hS.1.2.2 e he
      by_cases hlt : (P.δ e.1 e.2 : ℝ) < S e.2 - S e.1
      · have := hsl2 e (by linarith)
        rcases hσ with rfl | rfl <;> linarith [hzb e.1, hzb e.2]
      · have heq : (P.δ e.1 e.2 : ℝ) = S e.2 - S e.1 := le_antisymm h0 (not_lt.mp hlt)
        have h1 := hFp.1.2.2 e he; have h2 := hFm.1.2.2 e he
        rw [hYp, hYp] at h1; rw [hYm, hYm] at h2
        have hde : d e.1 = d e.2 := by
          have a1 : d e.1 ≤ d e.2 := by by_contra c; push_neg at c; nlinarith
          have a2 : d e.2 ≤ d e.1 := by by_contra c; push_neg at c; nlinarith
          linarith
        rw [hzeqd _ _ hde]; linarith
    · rintro ⟨i, j⟩ ⟨-, -, -, hle, hor⟩
      rw [hval, hval]
      simp only at hle hor ⊢
      rcases hor with hlt | hzz
      · have := hsl3 i j (by linarith)
        rcases hσ with rfl | rfl <;> linarith [hzb i, hzb j]
      · rw [hzz]; linarith
  intro hext
  rw [mem_extremePoints] at hext
  have := (hext.2 _ (hmem 1 (Or.inl rfl)) _ (hmem (-1) (Or.inr rfl))
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
      funext i; simp; ring⟩).1
  have h2 := congrFun this m
  simp [hzm] at h2
  linarith

end Stable6Aux

open Stable6Aux in
theorem solution {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    (IsAntiactive P S ↔ Maximal (· ∈ feasibleSet P) S) ∧
    (IsStable P S ↔ S ∈ (feasibleSet P).extremePoints ℝ) ∧
    (IsSemistable P S ↔ S ∈ (connectedComponentIn (feasibleSet P) S).extremePoints ℝ) ∧
    (IsPseudostable P S ↔
      ∀ O : Set (Fin (n + 2) × Fin (n + 2)), IsFeasibleOrder P O → O ⊆ scheduleOrder P S →
        S ∈ (orderPolytope P O).extremePoints ℝ) ∧
    (IsQuasistable P S ↔ S ∈ (orderPolytope P (scheduleOrder P S)).extremePoints ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hS, fun y hy hle => ?_⟩
      by_contra hne
      exact h ⟨y, ⟨hS, hy, fun e => hne (e ▸ le_refl _)⟩, hle, fun e => hne (e ▸ le_refl _)⟩
    · rintro ⟨-, h⟩
      refine ⟨hS, ?_⟩
      rintro ⟨S', ⟨-, h1, hne⟩, hle, -⟩
      exact hne (le_antisymm (h h1 hle) hle)
  · -- (b)
    exact uniform_iff (S ∈ feasibleSet P) hS hS (IsGlobalShift P S)
      (fun S' => ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hS, h.1, h.2⟩⟩)
  · -- (c)
    refine uniform_iff (S ∈ feasibleSet P) hS (mem_connectedComponentIn hS) (IsLocalShift P S)
      (fun S' => ⟨?_, ?_⟩)
    · rintro ⟨⟨-, -, hne⟩, x, hxc, hx0, hx1, hxF⟩
      refine ⟨?_, hne⟩
      have hsub := (isPreconnected_range hxc).subset_connectedComponentIn ⟨0, hx0⟩
        (by rintro _ ⟨t, rfl⟩; exact hxF t)
      exact hsub ⟨1, hx1⟩
    · rintro ⟨hC, hne⟩
      have hF' := connectedComponentIn_subset _ _ hC
      have J := comp_joined P hS hC
      exact ⟨⟨hS, hF', hne⟩, fun t => J.somePath t, J.somePath.continuous, J.somePath.source,
        J.somePath.target, J.somePath_mem⟩
  · -- (d)
    constructor
    · intro hps O hO hOS
      have hSO : S ∈ orderPolytope P O := ⟨hS.1, fun e he => (hOS he).2⟩
      rw [ext_iff _ hSO]
      rintro ⟨S', S'', h1, h2, hne, hne', lam, hlam, heq⟩
      obtain ⟨η, ⟨ho1, ho2⟩, hη1, hη0⟩ := (((small_order P S (S' - S)).and
        (small_order P S (S'' - S))).and ((ev_small 1).and self_mem_nhdsWithin)).exists
      have hη1 : η < 1 := hη1 one_pos
      have hη0 : (0:ℝ) < η := hη0
      have hval : ∀ (T : Fin (n + 2) → ℝ) i, (S + η • (T - S)) i = S i + η * (T - S) i :=
        fun T i => by simp
      have mem : ∀ T ∈ orderPolytope P O, S + η • (T - S) ∈ orderPolytope P O := fun T hT =>
        (convex_orderPolytope P O).add_smul_sub_mem hSO hT ⟨hη0.le, hη1.le⟩
      have ord : ∀ T : Fin (n + 2) → ℝ, (∀ i j : Fin (n + 2), S j < S i + (P.p i : ℝ) →
          S j + η * (T - S) j < S i + η * (T - S) i + (P.p i : ℝ)) →
          scheduleOrder P (S + η • (T - S)) ⊆ scheduleOrder P S := by
        rintro T hT ⟨i, j⟩ ⟨hij, hle⟩
        refine ⟨hij, ?_⟩
        by_contra c
        have := hT i j (not_le.mp c)
        simp only at hle
        rw [hval, hval] at hle
        linarith
      have neS : ∀ T : Fin (n + 2) → ℝ, T ≠ S → S + η • (T - S) ≠ S := by
        intro T hT hc
        apply hT
        funext i
        have := congrFun hc i
        rw [hval] at this
        simp only [Pi.sub_apply] at this
        rcases mul_eq_zero.mp (by linarith : η * (T i - S i) = 0) with h | h
        · linarith
        · linarith
      apply hps.2
      refine ⟨S + η • (S' - S), S + η • (S'' - S),
        ⟨⟨hS, hO.2.2 (mem S' h1), neS S' hne⟩, Or.inr (ord S' ho1)⟩,
        ⟨⟨hS, hO.2.2 (mem S'' h2), neS S'' hne'⟩, Or.inr (ord S'' ho2)⟩,
        neS S' hne, neS S'' hne', lam, hlam, ?_⟩
      funext i
      have := congrFun heq i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this ⊢
      rw [this]; ring
    · intro H
      refine ⟨hS, ?_⟩
      rintro ⟨S', S'', ⟨⟨-, h1F, -⟩, hmon1⟩, ⟨⟨-, h2F, -⟩, hmon2⟩, hne, hne', lam, hlam, heq⟩
      have seg1 := seg_feas P hS h1F hmon1
      have seg2 := seg_feas P hS h2F hmon2
      set d := S' - S with hd
      have hfeas : ∀ᶠ η in 𝓝[>] (0:ℝ), S + η • d ∈ feasibleSet P ∧ S - η • d ∈ feasibleSet P := by
        filter_upwards [ev_small 1, ev_small (-lam), self_mem_nhdsWithin] with η h1 h2 h0
        have h1 := h1 one_pos
        have h2 := h2 (by linarith)
        have h0 : (0:ℝ) < η := h0
        constructor
        · apply seg1
          refine ⟨1 - η, η, by linarith, h0.le, by ring, ?_⟩
          funext i; simp [hd]; ring
        · apply seg2
          have hl : lam ≠ 0 := hlam.ne
          refine ⟨1 - η / (-lam), η / (-lam), ?_, ?_, by ring, ?_⟩
          · rw [sub_nonneg, div_le_one (by linarith)]; linarith
          · exact div_nonneg h0.le (by linarith)
          · funext i
            have := congrFun heq i
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd] at this
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, hd]
            rw [show S'' i = S i + lam * (S' i - S i) by linarith]
            field_simp
            ring
      obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
      by_cases hdm : 0 < d m
      · obtain ⟨O, hO, hOS, hnot⟩ := core P hS m (fun i => hm i (Finset.mem_univ _)) hdm hfeas
        exact hnot (H O hO hOS)
      · obtain ⟨m', -, hm'⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
        have hdm' : 0 < (-d) m' := by
          obtain ⟨i, hi⟩ := Function.ne_iff.mp (sub_ne_zero.mpr hne)
          have h1 := hm i (Finset.mem_univ _)
          have h2 := hm' i (Finset.mem_univ _)
          simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
          rcases lt_or_gt_of_ne hi with h | h
          · linarith
          · exfalso; exact hdm (by linarith)
        have hfeas' : ∀ᶠ η in 𝓝[>] (0:ℝ), S + η • (-d) ∈ feasibleSet P ∧
            S - η • (-d) ∈ feasibleSet P := by
          filter_upwards [hfeas] with η h
          rw [smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
          exact ⟨h.2, h.1⟩
        obtain ⟨O, hO, hOS, hnot⟩ := core P hS m'
          (fun i => by simp only [Pi.neg_apply]; linarith [hm' i (Finset.mem_univ _)]) hdm' hfeas'
        exact hnot (H O hO hOS)
  · -- (e)
    exact uniform_iff (M := orderPolytope P (scheduleOrder P S)) (S ∈ feasibleSet P) hS ⟨hS.1, fun e he => he.2⟩ (IsOrderPreservingShift P S)
      (fun S' => ⟨fun ⟨⟨_, h1F, hne⟩, hsub⟩ => ⟨⟨h1F.1, fun e he => (hsub he).2⟩, hne⟩,
        fun ⟨hM, hne⟩ => ⟨⟨hS, feas_mono hS hM.1 (fun e he => ⟨he.1, hM.2 e he⟩), hne⟩,
          fun e he => ⟨he.1, hM.2 e he⟩⟩⟩)
