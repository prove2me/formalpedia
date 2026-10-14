-- Prove2me | solution 1 for TopkisRation.Levels.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:19:23.704847+00:00
-- url     : https://prove2.me/submissions/9a4d8d2f-c2bd-40bb-8418-95db34c4e979

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model



namespace TopkisRation.Levels

open MeasureTheory Filter Topology


theorem lemma_1_core {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : Set (E × F)) (hA : Convex ℝ A) (φ : E × F → ℝ) (hφ : ConvexOn ℝ A φ)
    (hbdd : ∀ u, BddBelow (φ '' {q | q ∈ A ∧ q.1 = u})) :
    ConvexOn ℝ (Prod.fst '' A) (fun u => sInf (φ '' {q | q ∈ A ∧ q.1 = u})) := by
  refine ⟨hA.linear_image (LinearMap.fst ℝ E F), ?_⟩
  rintro x ⟨p1, hp1, rfl⟩ y ⟨p2, hp2, rfl⟩ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hne1 : (φ '' {q | q ∈ A ∧ q.1 = p1.1}).Nonempty := ⟨φ p1, p1, ⟨hp1, rfl⟩, rfl⟩
  have hne2 : (φ '' {q | q ∈ A ∧ q.1 = p2.1}).Nonempty := ⟨φ p2, p2, ⟨hp2, rfl⟩, rfl⟩
  obtain ⟨_, ⟨q1, ⟨hq1A, hq1⟩, rfl⟩, hlt1⟩ :=
    exists_lt_of_csInf_lt hne1 (lt_add_of_pos_right (sInf (φ '' {q | q ∈ A ∧ q.1 = p1.1})) hε)
  obtain ⟨_, ⟨q2, ⟨hq2A, hq2⟩, rfl⟩, hlt2⟩ :=
    exists_lt_of_csInf_lt hne2 (lt_add_of_pos_right (sInf (φ '' {q | q ∈ A ∧ q.1 = p2.1})) hε)
  have hmem : a • q1 + b • q2 ∈ A := hA hq1A hq2A ha hb hab
  have hfst : (a • q1 + b • q2).1 = a • p1.1 + b • p2.1 := by simp [hq1, hq2]
  have h1 : sInf (φ '' {q | q ∈ A ∧ q.1 = a • p1.1 + b • p2.1}) ≤ φ (a • q1 + b • q2) :=
    csInf_le (hbdd _) ⟨_, ⟨hmem, hfst⟩, rfl⟩
  have h2 := hφ.2 hq1A hq2A ha hb hab
  simp only [smul_eq_mul] at h2
  have h3 : a * φ q1 ≤ a * (sInf (φ '' {q | q ∈ A ∧ q.1 = p1.1}) + ε) :=
    mul_le_mul_of_nonneg_left hlt1.le ha
  have h4 : b * φ q2 ≤ b * (sInf (φ '' {q | q ∈ A ∧ q.1 = p2.1}) + ε) :=
    mul_le_mul_of_nonneg_left hlt2.le hb
  have : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  nlinarith


variable {n : ℕ}

def Ocone (n : ℕ) : Set (ℝ × (Fin n → ℝ)) := Set.Ici (0:ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)

def Kset (n : ℕ) : Set (Fin n → ℝ) := {σ | 0 ≤ σ ∧ ∑ j, σ j ≤ 1}

lemma Kset_compact : IsCompact (Kset n) := by
  apply (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := 1)).of_isClosed_subset
  · rw [Kset, Set.ofPred_and]
    exact IsClosed.inter (isClosed_le continuous_const continuous_id)
      (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)
  · rintro σ ⟨h0, h1⟩
    refine ⟨h0, fun j => ?_⟩
    have : σ j ≤ ∑ k, σ k := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)
    simp only [Pi.one_apply]; linarith

noncomputable def sig (σ : Fin n → ℝ) : Fin n → ℝ :=
  fun j => max (σ j) 0 / max 1 (∑ k, max (σ k) 0)

noncomputable def sv (q : ℝ × (Fin n → ℝ)) (σ : Fin n → ℝ) : Fin n → ℝ :=
  fun j => min (max (q.2 j) 0) (max q.1 0 * sig σ j)

noncomputable def uv (q : ℝ × (Fin n → ℝ)) (σ : Fin n → ℝ) : Fin n → ℝ :=
  fun j => max (q.2 j) 0 - sv q σ j

lemma sig_nonneg (σ : Fin n → ℝ) (j : Fin n) : 0 ≤ sig σ j :=
  div_nonneg (le_max_right _ _) (le_trans zero_le_one (le_max_left _ _))

lemma sum_sig_le (σ : Fin n → ℝ) : ∑ j, sig σ j ≤ 1 := by
  unfold sig
  rw [← Finset.sum_div]
  have hD : (0:ℝ) < max 1 (∑ k, max (σ k) 0) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [div_le_one hD]
  exact le_max_right _ _

lemma sv_nonneg (q : ℝ × (Fin n → ℝ)) (σ) (j : Fin n) : 0 ≤ sv q σ j :=
  le_min (le_max_right _ _) (mul_nonneg (le_max_right _ _) (sig_nonneg σ j))

lemma sv_le (q : ℝ × (Fin n → ℝ)) (σ) (j : Fin n) : sv q σ j ≤ max (q.2 j) 0 := min_le_left _ _

lemma sum_sv_le (q : ℝ × (Fin n → ℝ)) (σ : Fin n → ℝ) : ∑ j, sv q σ j ≤ max q.1 0 := by
  calc ∑ j, sv q σ j ≤ ∑ j, max q.1 0 * sig σ j := Finset.sum_le_sum fun j _ => min_le_right _ _
    _ = max q.1 0 * ∑ j, sig σ j := by rw [Finset.mul_sum]
    _ ≤ max q.1 0 * 1 := mul_le_mul_of_nonneg_left (sum_sig_le σ) (le_max_right _ _)
    _ = max q.1 0 := mul_one _

lemma uv_nonneg (q : ℝ × (Fin n → ℝ)) (σ) : 0 ≤ uv q σ := fun j => by
  simp only [uv, Pi.zero_apply]; linarith [sv_le q σ j]

lemma sig_eq (σ : Fin n → ℝ) (hσ : σ ∈ Kset n) : sig σ = σ := by
  funext j
  have h0 : ∀ k, max (σ k) 0 = σ k := fun k => max_eq_left (hσ.1 k)
  simp only [sig, h0]
  rw [max_eq_left hσ.2, div_one]

lemma cont_sv : Continuous (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => sv p.1 p.2) := by
  apply continuous_pi; intro j
  simp only [sv, sig]
  apply Continuous.min
  · exact ((continuous_apply j).comp (continuous_snd.comp continuous_fst)).max continuous_const
  · apply Continuous.mul
    · exact (continuous_fst.comp continuous_fst).max continuous_const
    · apply Continuous.div
      · exact ((continuous_apply j).comp continuous_snd).max continuous_const
      · exact continuous_const.max (continuous_finsetSum _ fun k _ =>
          ((continuous_apply k).comp continuous_snd).max continuous_const)
      · intro x; exact (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'

lemma cont_uv : Continuous (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => uv p.1 p.2) := by
  apply continuous_pi; intro j
  simp only [uv]
  exact (((continuous_apply j).comp (continuous_snd.comp continuous_fst)).max continuous_const).sub
    ((continuous_apply j).comp cont_sv)

noncomputable def Fp (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ)
    (q : ℝ × (Fin n → ℝ)) (σ : Fin n → ℝ) : ℝ :=
  M.obj t G (max q.1 0) (fun j => max (q.2 j) 0) (uv q σ)

lemma obj_wsum (B : Fin n → ℝ) (q : ℝ × (Fin n → ℝ)) (σ : Fin n → ℝ) (hB : B = fun j => max (q.2 j) 0) :
    ∑ j, (B j - uv q σ j) = ∑ j, sv q σ j := by
  subst hB; simp [uv]

lemma Fp_cont (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ)
    (hh : ContinuousOn (M.h t) (Set.Ici 0)) (ha : 0 ≤ M.a t)
    (hG : ContinuousOn (fun q : ℝ × (Fin n → ℝ) => G q.1 q.2) (Ocone n)) :
    Continuous (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => Fp M t G p.1 p.2) := by
  have hw : ∀ p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ),
      max p.1.1 0 - ∑ j, ((fun j => max (p.1.2 j) 0) j - uv p.1 p.2 j)
        = max p.1.1 0 - ∑ j, sv p.1 p.2 j := fun p => by rw [obj_wsum _ p.1 p.2 rfl]
  have hwc : Continuous (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
      max p.1.1 0 - ∑ j, sv p.1 p.2 j) :=
    ((continuous_fst.comp continuous_fst).max continuous_const).sub
      (continuous_finsetSum _ fun j _ => (continuous_apply j).comp cont_sv)
  have hwn : ∀ p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ), 0 ≤ max p.1.1 0 - ∑ j, sv p.1 p.2 j :=
    fun p => by linarith [sum_sv_le p.1 p.2]
  unfold Fp Model.obj
  simp only [hw]
  apply Continuous.add
  · apply Continuous.add
    · simp only [dotProduct]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp cont_uv)
    · exact hh.comp_continuous hwc (fun p => hwn p)
  · have hc2 : Continuous (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        ((max p.1.1 0 - ∑ j, sv p.1 p.2 j), M.a t • uv p.1 p.2)) :=
      hwc.prodMk (cont_uv.const_smul (M.a t))
    exact hG.comp_continuous hc2 (fun p => ⟨hwn p, fun j => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ha (uv_nonneg _ _ j)⟩)

lemma obj_image_eq (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (q : ℝ × (Fin n → ℝ))
    (hq : q ∈ Ocone n) :
    M.obj t G q.1 q.2 '' feasible q.1 q.2 = (fun σ => Fp M t G q σ) '' Kset n := by
  obtain ⟨z, B⟩ := q
  obtain ⟨hz, hB⟩ := hq
  simp only [Set.mem_Ici] at hz hB
  replace hB : ∀ j, 0 ≤ B j := fun j => hB j
  have hzc : max z 0 = z := max_eq_left hz
  have hBc : (fun j => max (B j) 0) = B := funext fun j => max_eq_left (hB j)
  have huv : ∀ σ ∈ Kset n, uv (z, B) σ = fun j => B j - min (B j) (z * σ j) := by
    intro σ hσ; funext j
    simp only [uv, sv, sig_eq σ hσ]; rw [hzc, max_eq_left (hB j)]
  ext r; constructor
  · rintro ⟨u, ⟨hu0, huB, hus⟩, rfl⟩
    dsimp only at huB hus
    replace hu0 : ∀ j, 0 ≤ u j := fun j => hu0 j
    refine ⟨fun j => (B j - u j) / z, ⟨fun j => div_nonneg (by simp only [Pi.zero_apply]; linarith [huB j]) hz, ?_⟩, ?_⟩
    · rw [← Finset.sum_div]
      rcases hz.lt_or_eq with hz' | hz'
      · rw [div_le_one hz']; exact hus
      · rw [← hz', div_zero]; exact zero_le_one
    · have hσ : (fun j => (B j - u j) / z) ∈ Kset n := by
        refine ⟨fun j => div_nonneg (by simp only [Pi.zero_apply]; linarith [huB j]) hz, ?_⟩
        rw [← Finset.sum_div]
        rcases hz.lt_or_eq with hz' | hz'
        · rw [div_le_one hz']; exact hus
        · rw [← hz', div_zero]; exact zero_le_one
      have hu : uv (z, B) (fun j => (B j - u j) / z) = u := by
        rw [huv _ hσ]; funext j
        rcases hz.lt_or_eq with hz' | hz'
        · rw [mul_div_cancel₀ _ hz'.ne', min_eq_right (by linarith [hu0 j])]; ring
        · have hsum0 : ∑ k, (B k - u k) = 0 := by
            apply le_antisymm (by rw [hz']; exact hus)
            exact Finset.sum_nonneg fun k _ => by linarith [huB k]
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by linarith [huB k])).1 hsum0 j
            (Finset.mem_univ j)
          rw [← hz', zero_mul, min_eq_right (hB j)]; linarith
      simp only [Fp, hzc, hBc, hu]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨uv (z, B) σ, ⟨uv_nonneg _ _, fun j => ?_, ?_⟩, ?_⟩
    · simp only [uv]; linarith [sv_nonneg (z, B) σ j, max_eq_left (hB j)]
    · have := obj_wsum B (z, B) σ hBc.symm
      rw [this]; have := sum_sv_le (z, B) σ; simp only [hzc] at this; exact this
    · simp only [Fp, hzc, hBc]


def Growth (G : ℝ → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ Z : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, 0 ≤ z → z ≤ Z → ∀ b : Fin n → ℝ, 0 ≤ b →
    |G z b| ≤ C * (1 + ∑ j, b j)

structure GoodG (G : ℝ → (Fin n → ℝ) → ℝ) : Prop where
  conv : ConvexOn ℝ (Ocone n) (fun q => G q.1 q.2)
  cont : ContinuousOn (fun q => G q.1 q.2) (Ocone n)
  growth : Growth G

structure GoodStage (M : Model n) (t : ℕ) : Prop where
  hconv : ConvexOn ℝ (Set.Ici 0) (M.h t)
  hcont : ContinuousOn (M.h t) (Set.Ici 0)
  p0 : ∀ j, 0 ≤ M.p t j
  a0 : 0 ≤ M.a t

section stage
variable (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (hS : GoodStage M t) (hG : GoodG G)
include hS hG

lemma image_compact (q : ℝ × (Fin n → ℝ)) (hq : q ∈ Ocone n) :
    IsCompact (M.obj t G q.1 q.2 '' feasible q.1 q.2) := by
  rw [obj_image_eq M t G q hq]
  apply Kset_compact.image
  exact (Fp_cont M t G hS.hcont hS.a0 hG.cont).comp (Continuous.prodMk_right q)

lemma feasible_self (q : ℝ × (Fin n → ℝ)) (hq : q ∈ Ocone n) : q.2 ∈ feasible q.1 q.2 :=
  ⟨hq.2, le_rfl, by simp only [sub_self, Finset.sum_const_zero]; exact hq.1⟩

lemma stage_min (q : ℝ × (Fin n → ℝ)) (hq : q ∈ Ocone n) :
    ∃ u ∈ feasible q.1 q.2, M.stage t G q.1 q.2 = M.obj t G q.1 q.2 u ∧
      ∀ u' ∈ feasible q.1 q.2, M.obj t G q.1 q.2 u ≤ M.obj t G q.1 q.2 u' := by
  have hc := image_compact M t G hS hG q hq
  have hne : (M.obj t G q.1 q.2 '' feasible q.1 q.2).Nonempty :=
    ⟨_, q.2, feasible_self M t G hS hG q hq, rfl⟩
  obtain ⟨u, hu, hEq⟩ := hc.sInf_mem hne
  refine ⟨u, hu, hEq.symm, fun u' hu' => ?_⟩
  rw [hEq]; exact csInf_le hc.bddBelow ⟨u', hu', rfl⟩

lemma stage_cont : ContinuousOn (fun q : ℝ × (Fin n → ℝ) => M.stage t G q.1 q.2) (Ocone n) := by
  have hc := IsCompact.continuous_sInf (f := fun q σ => Fp M t G q σ) (Kset_compact (n := n))
    (Fp_cont M t G hS.hcont hS.a0 hG.cont)
  refine hc.continuousOn.congr fun q hq => ?_
  simp only [Model.stage]
  rw [obj_image_eq M t G q hq]

lemma stage_growth : Growth (M.stage t G) := by
  intro Z
  obtain ⟨CG, hCG0, hCG⟩ := hG.growth Z
  obtain ⟨H, hH⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Z)).exists_bound_of_continuousOn
    (hS.hcont.mono Set.Icc_subset_Ici_self)
  set P := ∑ j, M.p t j
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => hS.p0 j
  have hPj : ∀ j, M.p t j ≤ P := fun j => Finset.single_le_sum (fun k _ => hS.p0 k) (Finset.mem_univ j)
  refine ⟨P + max H 0 + CG * (1 + M.a t), by have := hS.a0; positivity, ?_⟩
  intro z hz hzZ B hB
  have hq : (z, B) ∈ Ocone n := ⟨hz, hB⟩
  obtain ⟨u, ⟨hu0, huB, hus⟩, hEq, hmin⟩ := stage_min M t G hS hG (z, B) hq
  simp only at hEq hmin hu0 huB hus
  have hSB : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun j _ => hB j
  have hsa : ∀ v : Fin n → ℝ, ∑ j, (M.a t • v) j = M.a t * ∑ j, v j := fun v => by
    simp [Finset.mul_sum]
  -- upper bound
  have hup := hmin B (feasible_self M t G hS hG (z, B) hq)
  have hobjB : M.obj t G z B B ≤ P * ∑ j, B j + max H 0 + CG * (1 + M.a t * ∑ j, B j) := by
    simp only [Model.obj, sub_self, Finset.sum_const_zero, sub_zero]
    have h1 : M.p t ⬝ᵥ B ≤ P * ∑ j, B j := by
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hPj j) (hB j)
    have h2 : M.h t z ≤ max H 0 := by
      have := hH z ⟨hz, hzZ⟩; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (M.h t z), le_max_left H 0]
    have h3 := hCG z hz hzZ (M.a t • B) (fun j => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hB j))
    rw [hsa] at h3
    linarith [le_abs_self (G z (M.a t • B))]
  -- lower bound
  have hw0 : 0 ≤ z - ∑ j, (B j - u j) := by linarith
  have hwZ : z - ∑ j, (B j - u j) ≤ Z := by
    have : 0 ≤ ∑ j, (B j - u j) := Finset.sum_nonneg fun j _ => by linarith [huB j]
    linarith
  have hlow : -(max H 0) - CG * (1 + M.a t * ∑ j, B j) ≤ M.obj t G z B u := by
    simp only [Model.obj]
    have h1 : 0 ≤ M.p t ⬝ᵥ u := Finset.sum_nonneg fun j _ => mul_nonneg (hS.p0 j) (hu0 j)
    have h2 : -(max H 0) ≤ M.h t (z - ∑ j, (B j - u j)) := by
      have := hH _ ⟨hw0, hwZ⟩; rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (M.h t (z - ∑ j, (B j - u j))), le_max_left H 0]
    have h3 := hCG _ hw0 hwZ (M.a t • u) (fun j => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu0 j))
    rw [hsa] at h3
    have hsu : M.a t * ∑ j, u j ≤ M.a t * ∑ j, B j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => huB j) hS.a0
    have : CG * (1 + M.a t * ∑ j, u j) ≤ CG * (1 + M.a t * ∑ j, B j) :=
      mul_le_mul_of_nonneg_left (by linarith) hCG0
    linarith [neg_abs_le (G (z - ∑ j, (B j - u j)) (M.a t • u))]
  rw [abs_le]
  have hH0 : 0 ≤ max H 0 := le_max_right _ _
  have ha0 := hS.a0
  constructor
  · rw [hEq]; nlinarith [mul_nonneg hP0 hSB, mul_nonneg hH0 hSB, mul_nonneg hCG0 hSB,
      mul_nonneg (mul_nonneg hCG0 ha0) hSB]
  · rw [hEq]; nlinarith [mul_nonneg hP0 hSB, mul_nonneg hH0 hSB, mul_nonneg hCG0 hSB,
      mul_nonneg (mul_nonneg hCG0 ha0) hSB, mul_nonneg hCG0 ha0]

end stage


section stage2
variable (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (hS : GoodStage M t) (hG : GoodG G)
include hS hG

lemma stage_conv : ConvexOn ℝ (Ocone n) (fun q : ℝ × (Fin n → ℝ) => M.stage t G q.1 q.2) := by
  let A : Set ((ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) :=
    {r | r.1 ∈ Ocone n ∧ r.2 ∈ feasible r.1.1 r.1.2}
  let φ : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ := fun r => M.obj t G r.1.1 r.1.2 r.2
  have hOc : Convex ℝ (Ocone n) := (convex_Ici 0).prod (convex_Ici 0)
  have hwlin : ∀ (r1 r2 : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) (α β : ℝ),
      (α • r1 + β • r2).1.1 - ∑ j, ((α • r1 + β • r2).1.2 j - (α • r1 + β • r2).2 j) =
        α * (r1.1.1 - ∑ j, (r1.1.2 j - r1.2 j)) + β * (r2.1.1 - ∑ j, (r2.1.2 j - r2.2 j)) := by
    intro r1 r2 α β
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have : ∑ j, (α * r1.1.2 j + β * r2.1.2 j - (α * r1.2 j + β * r2.2 j)) =
        α * ∑ j, (r1.1.2 j - r1.2 j) + β * ∑ j, (r2.1.2 j - r2.2 j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  have hA : Convex ℝ A := by
    rintro r1 ⟨hr1O, hu10, hu1B, hu1s⟩ r2 ⟨hr2O, hu20, hu2B, hu2s⟩ α β hα hβ hαβ
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hOc hr1O hr2O hα hβ hαβ
      simpa using this
    · intro j; simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      exact add_nonneg (mul_nonneg hα (hu10 j)) (mul_nonneg hβ (hu20 j))
    · intro j; simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hu1B j) hα) (mul_le_mul_of_nonneg_left (hu2B j) hβ)
    · have h := hwlin r1 r2 α β
      have e1 := mul_le_mul_of_nonneg_left hu1s hα
      have e2 := mul_le_mul_of_nonneg_left hu2s hβ
      have : (α • r1 + β • r2).1.1 = α * r1.1.1 + β * r2.1.1 := by simp
      nlinarith
  have hφ : ConvexOn ℝ A φ := by
    refine ⟨hA, ?_⟩
    rintro r1 ⟨hr1O, hu10, hu1B, hu1s⟩ r2 ⟨hr2O, hu20, hu2B, hu2s⟩ α β hα hβ hαβ
    simp only [φ, Model.obj, smul_eq_mul]
    rw [hwlin r1 r2 α β]
    set w1 := r1.1.1 - ∑ j, (r1.1.2 j - r1.2 j)
    set w2 := r2.1.1 - ∑ j, (r2.1.2 j - r2.2 j)
    have hw1 : 0 ≤ w1 := by simp only [w1]; linarith
    have hw2 : 0 ≤ w2 := by simp only [w2]; linarith
    have hp : M.p t ⬝ᵥ (α • r1 + β • r2).2 = α * (M.p t ⬝ᵥ r1.2) + β * (M.p t ⬝ᵥ r2.2) := by
      simp [dotProduct_add, dotProduct_smul]
    have hh := hS.hconv.2 (Set.mem_Ici.2 hw1) (Set.mem_Ici.2 hw2) hα hβ hαβ
    simp only [smul_eq_mul] at hh
    have hm1 : ((w1, M.a t • r1.2) : ℝ × (Fin n → ℝ)) ∈ Ocone n :=
      ⟨hw1, fun j => by simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu10 j)⟩
    have hm2 : ((w2, M.a t • r2.2) : ℝ × (Fin n → ℝ)) ∈ Ocone n :=
      ⟨hw2, fun j => by simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu20 j)⟩
    have hg := hG.conv.2 hm1 hm2 hα hβ hαβ
    simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at hg
    have he : α • M.a t • r1.2 + β • M.a t • r2.2 = M.a t • (α • r1 + β • r2).2 := by
      simp only [Prod.snd_add, Prod.smul_snd, smul_add]
      rw [smul_comm α, smul_comm β]
    rw [he] at hg
    rw [hp]
    nlinarith
  have hbdd : ∀ q, BddBelow (φ '' {r | r ∈ A ∧ r.1 = q}) := by
    intro q
    by_cases hq : q ∈ Ocone n
    · apply (image_compact M t G hS hG q hq).bddBelow.mono
      rintro _ ⟨r, ⟨⟨_, hr⟩, rfl⟩, rfl⟩
      exact ⟨r.2, hr, rfl⟩
    · have : {r | r ∈ A ∧ r.1 = q} = ∅ := by
        ext r; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨hr, _⟩ rfl; exact hq hr
      rw [this, Set.image_empty]; exact bddBelow_empty
  have h1 := lemma_1_core A hA φ hφ hbdd
  have hfst : Prod.fst '' A = Ocone n := by
    ext q; constructor
    · rintro ⟨r, ⟨hr, _⟩, rfl⟩; exact hr
    · intro hq; exact ⟨(q, q.2), ⟨hq, feasible_self M t G hS hG q hq⟩, rfl⟩
  rw [hfst] at h1
  refine h1.congr fun q hq => ?_
  simp only [Model.stage]
  congr 1
  ext x; constructor
  · rintro ⟨r, ⟨⟨_, hr⟩, rfl⟩, rfl⟩; exact ⟨r.2, hr, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨(q, u), ⟨⟨hq, hu⟩, rfl⟩, rfl⟩

lemma stage_good : GoodG (M.stage t G) :=
  ⟨stage_conv M t G hS hG, stage_cont M t G hS hG, stage_growth M t G hS hG⟩

end stage2


section gstep
variable (S : ℝ → (Fin n → ℝ) → ℝ) (hSg : GoodG S) (μ : Measure (Fin n → ℝ))
  [IsProbabilityMeasure μ] (hμ0 : ∀ᵐ x ∂μ, 0 ≤ x)
  (hμm : ∀ j, Integrable (fun x : Fin n → ℝ => x j) μ)
include hSg hμ0

lemma meas_shift (z : ℝ) (hz : 0 ≤ z) (b : Fin n → ℝ) (hb : 0 ≤ b) :
    AEStronglyMeasurable (fun x => S z (b + x)) μ := by
  have hc : ContinuousOn (fun x : Fin n → ℝ => S z (b + x)) (Set.Ici 0) :=
    hSg.cont.comp (continuous_const.prodMk (continuous_const.add continuous_id)).continuousOn
      (fun x hx => ⟨hz, by simpa using add_nonneg hb hx⟩)
  have := hc.aestronglyMeasurable (μ := μ) measurableSet_Ici
  rwa [Measure.restrict_eq_self_of_ae_mem (s := Set.Ici 0) hμ0] at this

include hμm

omit hSg hμ0 in
lemma bound_int (c d : ℝ) : Integrable (fun x : Fin n → ℝ => c * (d + ∑ j, x j)) μ :=
  ((integrable_const d).add (integrable_finsetSum _ fun j _ => hμm j)).const_mul c

omit hSg hμ0 in
lemma bound_integral (c d : ℝ) : ∫ x, c * (d + ∑ j, x j) ∂μ = c * (d + ∑ j, ∫ x, x j ∂μ) := by
  rw [integral_const_mul, integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => hμm j),
    integral_const, integral_finset_sum _ fun j _ => hμm j]
  simp

lemma bound_ae (C : ℝ) (z : ℝ) (b : Fin n → ℝ) (hb : 0 ≤ b)
    (hC : |S z (b + 0)| ≤ C * (1 + ∑ j, (b + 0) j) → True)
    (h : ∀ x : Fin n → ℝ, 0 ≤ x → |S z (b + x)| ≤ C * (1 + ∑ j, (b + x) j)) :
    ∀ᵐ x ∂μ, ‖S z (b + x)‖ ≤ C * ((1 + ∑ j, b j) + ∑ j, x j) := by
  filter_upwards [hμ0] with x hx
  rw [Real.norm_eq_abs]
  have := h x hx
  simp only [Pi.add_apply, Finset.sum_add_distrib] at this
  linarith

lemma int_shift (z : ℝ) (hz : 0 ≤ z) (b : Fin n → ℝ) (hb : 0 ≤ b) :
    Integrable (fun x => S z (b + x)) μ := by
  obtain ⟨C, hC0, hC⟩ := hSg.growth z
  refine (bound_int μ hμm C (1 + ∑ j, b j)).mono' (meas_shift S hSg μ hμ0 z hz b hb) ?_
  exact bound_ae S hSg μ hμ0 hμm C z b hb (fun _ => trivial)
    (fun x hx => hC z hz le_rfl (b + x) (add_nonneg hb hx))

lemma mean_nonneg : 0 ≤ ∑ j, ∫ x, x j ∂μ :=
  Finset.sum_nonneg fun j _ => integral_nonneg_of_ae (by filter_upwards [hμ0] with x hx; exact hx j)

lemma gstep_good : GoodG (fun z b => ∫ x, S z (b + x) ∂μ) := by
  have hOc : Convex ℝ (Ocone n) := (convex_Ici 0).prod (convex_Ici 0)
  have hm := mean_nonneg S hSg μ hμ0 hμm
  refine ⟨⟨hOc, ?_⟩, ?_, ?_⟩
  · rintro q1 hq1 q2 hq2 α β hα hβ hαβ
    have hq := hOc hq1 hq2 hα hβ hαβ
    simp only [smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((int_shift S hSg μ hμ0 hμm _ hq1.1 _ hq1.2).const_mul α)
        ((int_shift S hSg μ hμ0 hμm _ hq2.1 _ hq2.2).const_mul β)]
    apply integral_mono_ae (int_shift S hSg μ hμ0 hμm _ hq.1 _ hq.2)
      (((int_shift S hSg μ hμ0 hμm _ hq1.1 _ hq1.2).const_mul α).add
        ((int_shift S hSg μ hμ0 hμm _ hq2.1 _ hq2.2).const_mul β))
    filter_upwards [hμ0] with x hx
    have hm1 : ((q1.1, q1.2 + x) : ℝ × (Fin n → ℝ)) ∈ Ocone n := ⟨hq1.1, add_nonneg hq1.2 hx⟩
    have hm2 : ((q2.1, q2.2 + x) : ℝ × (Fin n → ℝ)) ∈ Ocone n := ⟨hq2.1, add_nonneg hq2.2 hx⟩
    have hc := hSg.conv.2 hm1 hm2 hα hβ hαβ
    have he : α • ((q1.1, q1.2 + x) : ℝ × (Fin n → ℝ)) + β • (q2.1, q2.2 + x) =
        ((α • q1 + β • q2).1, (α • q1 + β • q2).2 + x) := by
      refine Prod.ext ?_ ?_
      · simp
      · funext j
        simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        linear_combination (x j) * hαβ
    rw [he] at hc
    simpa only [smul_eq_mul, Pi.add_apply] using hc
  · intro q0 hq0
    obtain ⟨C, hC0, hC⟩ := hSg.growth (q0.1 + 1)
    have hev1 : ∀ᶠ q in 𝓝[Ocone n] q0, q.1 < q0.1 + 1 :=
      ((continuous_fst.tendsto q0).mono_left nhdsWithin_le_nhds).eventually_lt_const (lt_add_one _)
    have hev2 : ∀ᶠ q in 𝓝[Ocone n] q0, ∑ j, q.2 j < ∑ j, q0.2 j + 1 :=
      (((continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd).tendsto q0).mono_left
          nhdsWithin_le_nhds).eventually_lt_const (lt_add_one _)
    have hev3 : ∀ᶠ q in 𝓝[Ocone n] q0, q ∈ Ocone n := self_mem_nhdsWithin
    apply continuousWithinAt_of_dominated (bound := fun x => C * ((1 + (∑ j, q0.2 j + 1)) + ∑ j, x j))
    · filter_upwards [hev3] with q hq
      exact meas_shift S hSg μ hμ0 q.1 hq.1 q.2 hq.2
    · filter_upwards [hev1, hev2, hev3] with q h1 h2 hq
      have hb := bound_ae S hSg μ hμ0 hμm C q.1 q.2 hq.2 (fun _ => trivial)
        (fun x hx => hC q.1 hq.1 h1.le (q.2 + x) (add_nonneg hq.2 hx))
      filter_upwards [hb, hμ0] with x hx hx0
      have : 0 ≤ ∑ j, x j := Finset.sum_nonneg fun j _ => hx0 j
      nlinarith
    · exact bound_int μ hμm _ _
    · filter_upwards [hμ0] with x hx
      exact (hSg.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousOn
        (fun q hq => ⟨hq.1, add_nonneg hq.2 hx⟩)).continuousWithinAt hq0
  · intro Z
    obtain ⟨C, hC0, hC⟩ := hSg.growth Z
    refine ⟨C * (1 + ∑ j, ∫ x, x j ∂μ), by positivity, ?_⟩
    intro z hz hzZ b hb
    have hb' := bound_ae S hSg μ hμ0 hμm C z b hb (fun _ => trivial)
        (fun x hx => hC z hz hzZ (b + x) (add_nonneg hb hx))
    have := norm_integral_le_of_norm_le (bound_int μ hμm C (1 + ∑ j, b j)) hb'
    rw [bound_integral μ hμm, Real.norm_eq_abs] at this
    have hSb : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun j _ => hb j
    refine this.trans ?_
    nlinarith [mul_nonneg (mul_nonneg hC0 hm) hSb]

end gstep


lemma v2_upper (M : Model n) (hM : M.Standing) :
    ∃ L' : ℝ, 0 ≤ L' ∧ ∀ s, 0 ≤ s → M.v₂ (-s) ≤ M.v₂ 0 + L' * s := by
  obtain ⟨L, hL⟩ := hM.v₂_slope
  refine ⟨|L|, abs_nonneg _, fun s hs => ?_⟩
  rcases hs.lt_or_eq with hs | hs
  · have key : L ≤ (M.v₂ 0 - M.v₂ (-s)) / (0 - -s) := by
      have h1 := hL (-s)
      have h2 : rightDeriv M.v₂ (-s) ≤ (((M.v₂ 0 - M.v₂ (-s)) / (0 - -s) : ℝ) : EReal) := by
        unfold rightDeriv
        apply liminf_le_of_frequently_le'
        apply Filter.Eventually.frequently
        filter_upwards [Ioo_mem_nhdsGT hs] with ε hε
        rw [EReal.coe_le_coe_iff]
        have := hM.v₂_convex.secant_mono (a := -s) (x := -s + ε) (y := 0) (Set.mem_univ _)
          (Set.mem_univ _) (Set.mem_univ _) (by linarith [hε.1]) (by linarith) (by linarith [hε.2])
        have e : -s + ε - -s = ε := by ring
        rw [e] at this; exact this
      exact EReal.coe_le_coe_iff.1 (h1.trans h2)
    rw [le_div_iff₀ (by linarith)] at key
    nlinarith [neg_abs_le L, le_abs_self L]
  · subst hs; simp

lemma v2_lower (M : Model n) (hM : M.Standing) :
    ∀ s, 0 ≤ s → M.v₂ 0 - |M.v₂ 1 - M.v₂ 0| * s ≤ M.v₂ (-s) := by
  intro s hs
  rcases hs.lt_or_eq with hs | hs
  · have := hM.v₂_convex.slope_mono_adjacent (x := -s) (y := 0) (z := 1) (Set.mem_univ _)
      (Set.mem_univ _) (by linarith) one_pos
    rw [show (0:ℝ) - -s = s by ring, show (1:ℝ) - 0 = 1 by ring, div_one,
      div_le_iff₀ hs] at this
    nlinarith [le_abs_self (M.v₂ 1 - M.v₂ 0)]
  · subst hs; simp

lemma g0_good (M : Model n) (hM : M.Standing) : GoodG (M.g 0) := by
  have hOc : Convex ℝ (Ocone n) := (convex_Ici 0).prod (convex_Ici 0)
  have hylin : ∀ (q1 q2 : ℝ × (Fin n → ℝ)) (α β : ℝ),
      (α • q1 + β • q2).1 - ∑ j, (α • q1 + β • q2).2 j =
        α * (q1.1 - ∑ j, q1.2 j) + β * (q2.1 - ∑ j, q2.2 j) := by
    intro q1 q2 α β
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  refine ⟨⟨hOc, ?_⟩, ?_, ?_⟩
  · rintro q1 hq1 q2 hq2 α β hα hβ hαβ
    simp only [Model.g]
    rw [hylin]
    have h1 := hM.v₁_convex.2 hq1.1 hq2.1 hα hβ hαβ
    have h2 := hM.v₂_convex.2 (Set.mem_univ (q1.1 - ∑ j, q1.2 j))
      (Set.mem_univ (q2.1 - ∑ j, q2.2 j)) hα hβ hαβ
    simp only [smul_eq_mul, Prod.fst_add, Prod.smul_fst] at h1 h2 ⊢
    linarith
  · simp only [Model.g]
    apply ContinuousOn.add
    · exact hM.v₁_cont.comp continuous_fst.continuousOn (fun q hq => hq.1)
    · exact (hM.v₂_cont.comp (continuous_fst.sub (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp continuous_snd))).continuousOn
  · intro Z
    obtain ⟨H1, hH1⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Z)).exists_bound_of_continuousOn
      (hM.v₁_cont.mono Set.Icc_subset_Ici_self)
    obtain ⟨H2, hH2⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Z)).exists_bound_of_continuousOn
      hM.v₂_cont.continuousOn
    obtain ⟨L', hL'0, hL'⟩ := v2_upper M hM
    have hD := v2_lower M hM
    have hD0 : 0 ≤ |M.v₂ 1 - M.v₂ 0| := abs_nonneg _
    refine ⟨max H1 0 + max H2 0 + |M.v₂ 0| + L' + |M.v₂ 1 - M.v₂ 0|, by positivity, ?_⟩
    intro z hz hzZ b hb
    simp only [Model.g]
    have hSb : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun j _ => hb j
    have e1 : |M.v₁ z| ≤ max H1 0 := by
      have := hH1 z ⟨hz, hzZ⟩; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    have e2 : |M.v₂ (z - ∑ j, b j)| ≤
        max H2 0 + |M.v₂ 0| + (L' + |M.v₂ 1 - M.v₂ 0|) * ∑ j, b j := by
      rcases le_or_gt 0 (z - ∑ j, b j) with hy | hy
      · have := hH2 _ ⟨hy, by linarith⟩; rw [Real.norm_eq_abs] at this
        nlinarith [le_max_left H2 0, abs_nonneg (M.v₂ 0), mul_nonneg (add_nonneg hL'0 hD0) hSb]
      · have hs : 0 ≤ ∑ j, b j - z := by linarith
        have hy' : z - ∑ j, b j = -(∑ j, b j - z) := by ring
        rw [hy']
        have u1 := hL' _ hs
        have u2 := hD _ hs
        have hsS : ∑ j, b j - z ≤ ∑ j, b j := by linarith
        rw [abs_le]; constructor
        · nlinarith [le_max_right H2 0, neg_abs_le (M.v₂ 0), mul_le_mul_of_nonneg_left hsS hD0,
            mul_le_mul_of_nonneg_left hsS hL'0, mul_nonneg hL'0 hSb]
        · nlinarith [le_max_right H2 0, le_abs_self (M.v₂ 0), mul_le_mul_of_nonneg_left hsS hD0,
            mul_le_mul_of_nonneg_left hsS hL'0, mul_nonneg hD0 hSb]
    have e3 := abs_add_le (M.v₁ z) (M.v₂ (z - ∑ j, b j))
    have hH10 : 0 ≤ max H1 0 := le_max_right _ _
    have hH20 : 0 ≤ max H2 0 := le_max_right _ _
    nlinarith [mul_nonneg hH10 hSb, mul_nonneg hH20 hSb, mul_nonneg (abs_nonneg (M.v₂ 0)) hSb]

lemma stageOf (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k) :
    GoodStage M t :=
  ⟨hM.h_convex t ht, hM.h_cont t ht, hM.p_nonneg t ht, hM.a_nonneg t ht⟩

lemma g_good (M : Model n) (hM : M.Standing) : ∀ t, t ≤ M.k → GoodG (M.g t)
  | 0, _ => g0_good M hM
  | t + 1, ht => by
    have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
    have hS := stage_good M (t+1) (M.g t) (stageOf M hM _ ht') (g_good M hM t (by omega))
    haveI := hM.μ_prob _ ht'
    exact gstep_good _ hS (M.μ (t+1)) (hM.μ_nonneg _ ht') (hM.μ_mean _ ht')

lemma f_good (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k) :
    GoodG (M.f t) :=
  stage_good M t (M.g (t-1)) (stageOf M hM t ht) (g_good M hM (t-1) (by
    have := (Finset.mem_Icc.1 ht).2; omega))

open MeasureTheory in
theorem lemma_2_core {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k) :
    (ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.g t q.1 q.2) ∧
      ContinuousOn (fun q => M.g t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t →
      ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.f t q.1 q.2) ∧
      ContinuousOn (fun q => M.f t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
      ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
        ∀ u' ∈ feasible z B, M.obj t (M.g (t - 1)) z B u ≤ M.obj t (M.g (t - 1)) z B u') ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => M.f t z (b + x)) (M.μ t)) := by
  have hg := g_good M hM t ht
  refine ⟨⟨hg.conv, hg.cont⟩, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have hf := f_good M hM t (Finset.mem_Icc.2 ⟨h1, ht⟩)
    exact ⟨hf.conv, hf.cont⟩
  · intro z hz B hB
    have ht' : t ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨h1, ht⟩
    exact stage_min M t (M.g (t-1)) (stageOf M hM t ht') (g_good M hM (t-1) (by omega)) (z, B) ⟨hz, hB⟩
  · intro z hz b hb
    have ht' : t ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨h1, ht⟩
    haveI := hM.μ_prob _ ht'
    exact int_shift (M.f t) (f_good M hM t ht') (M.μ t) (hM.μ_nonneg _ ht') (hM.μ_mean _ ht') z hz b hb

end TopkisRation.Levels

open TopkisRation.Levels
open MeasureTheory

theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k) :
    (ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.g t q.1 q.2) ∧
      ContinuousOn (fun q => M.g t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t →
      ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.f t q.1 q.2) ∧
      ContinuousOn (fun q => M.f t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
      ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
        ∀ u' ∈ feasible z B, M.obj t (M.g (t - 1)) z B u ≤ M.obj t (M.g (t - 1)) z B u') ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => M.f t z (b + x)) (M.μ t)) := by
  exact lemma_2_core M hM t ht
