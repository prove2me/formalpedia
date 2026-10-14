-- Prove2me | solution 1 for TopkisRation.Levels.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:36:42.724981+00:00
-- url     : https://prove2.me/submissions/cc7edcf9-f82d-412a-bd33-501aeab85b3f

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_Levels_Split



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


lemma crit_generic (φ : ℝ → ℝ) (hc : ConvexOn ℝ (Set.Ici 0) φ) (hk : ContinuousOn φ (Set.Ici 0)) :
    ∃! zbar : WithTop ℝ, IsCriticalLevel φ zbar := by
  have hex : ∃ zbar : WithTop ℝ, IsCriticalLevel φ zbar := by
    by_cases hmin : ∃ x, 0 ≤ x ∧ ∀ y, 0 ≤ y → φ x ≤ φ y
    · obtain ⟨x0, hx0, hmin0⟩ := hmin
      set Ms := Set.Ici (0:ℝ) ∩ φ ⁻¹' Set.Iic (φ x0)
      have hcl : IsClosed Ms := hk.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
      have hne : Ms.Nonempty := ⟨x0, Set.mem_Ici.2 hx0, Set.mem_preimage.2 (Set.mem_Iic.2 le_rfl)⟩
      have hbdd : BddBelow Ms := ⟨0, fun y hy => hy.1⟩
      have hmem := hcl.csInf_mem hne hbdd
      refine ⟨(sInf Ms : ℝ), Or.inr ⟨sInf Ms, rfl, hmem.1, fun y hy => ?_, fun y hy hy' => ?_⟩⟩
      · exact le_trans hmem.2 (hmin0 y hy)
      · exact csInf_le hbdd ⟨hy, hy' x0 hx0⟩
    · push_neg at hmin
      refine ⟨⊤, Or.inl ⟨rfl, fun a ha b hb hab => ?_⟩⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨c, hcmem, hcmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := b)).exists_isMinOn
        ⟨b, Set.mem_Icc.2 ⟨hb, le_rfl⟩⟩ (hk.mono Set.Icc_subset_Ici_self)
      obtain ⟨y, hy, hlt⟩ := hmin c hcmem.1
      rcases le_or_gt y b with hyb | hyb
      · exact absurd (hcmin ⟨hy, hyb⟩) (not_le.2 hlt)
      · have hs := hc.slope_mono_adjacent ha (Set.mem_Ici.2 hy) hab hyb
        have h1 : 0 ≤ (φ b - φ a) / (b - a) := div_nonneg (by linarith) (by linarith)
        have h2 : 0 ≤ φ y - φ b := by
          have := mul_nonneg (h1.trans hs) (le_of_lt (sub_pos.2 hyb))
          rwa [div_mul_cancel₀ _ (sub_pos.2 hyb).ne'] at this
        have := hcmin ⟨hb, le_rfl⟩
        simp only [Set.mem_setOf_eq] at this
        linarith
  obtain ⟨zbar, hz⟩ := hex
  refine ⟨zbar, hz, fun z' hz' => ?_⟩
  have key : ∀ (z1 z2 : WithTop ℝ), IsCriticalLevel φ z1 → IsCriticalLevel φ z2 → z1 = z2 := by
    intro z1 z2 h1 h2
    rcases h1 with ⟨rfl, ha1⟩ | ⟨x1, rfl, hx1, hm1, hl1⟩ <;>
      rcases h2 with ⟨rfl, ha2⟩ | ⟨x2, rfl, hx2, hm2, hl2⟩
    · rfl
    · exact absurd (hm2 (x2 + 1) (by linarith)) (not_le.2 (ha1 hx2 (Set.mem_Ici.2 (by linarith)) (by linarith)))
    · exact absurd (hm1 (x1 + 1) (by linarith)) (not_le.2 (ha2 hx1 (Set.mem_Ici.2 (by linarith)) (by linarith)))
    · have := hl1 x2 hx2 hm2
      have := hl2 x1 hx1 hm1
      congr 1; linarith
  exact key _ _ hz' hz

theorem criticalLevel_exists_core {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.k) :
    ∀ j : Fin n, ∃! zbar : WithTop ℝ, IsCriticalLevel (M.levelObj t j) zbar := by
  intro j
  have hS := stageOf M hM t ht
  have hg := g_good M hM (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
  have hmem : ∀ w : ℝ, 0 ≤ w → ((w, M.a t • w • Pi.single j (1:ℝ)) : ℝ × (Fin n → ℝ)) ∈ Ocone n := by
    intro w hw
    refine ⟨hw, fun i => ?_⟩
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hS.a0 (mul_nonneg hw (by by_cases h : i = j <;> simp [Pi.single_apply, h]))
  apply crit_generic
  · refine ⟨convex_Ici 0, fun w1 hw1 w2 hw2 α β hα hβ hαβ => ?_⟩
    simp only [Model.levelObj, smul_eq_mul]
    have hh := hS.hconv.2 hw1 hw2 hα hβ hαβ
    have hgc := hg.conv.2 (hmem w1 hw1) (hmem w2 hw2) hα hβ hαβ
    have he : α • ((w1, M.a t • w1 • Pi.single j (1:ℝ)) : ℝ × (Fin n → ℝ)) +
        β • (w2, M.a t • w2 • Pi.single j (1:ℝ)) =
        (α * w1 + β * w2, M.a t • (α * w1 + β * w2) • Pi.single j (1:ℝ)) := by
      refine Prod.ext (by simp) ?_
      funext i
      simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he] at hgc
    simp only [smul_eq_mul] at hh hgc
    nlinarith
  · unfold Model.levelObj
    apply ContinuousOn.add
    · exact (continuous_const.mul continuous_id).continuousOn.add hS.hcont
    · have hcomp : Continuous (fun w : ℝ => ((w, M.a t • w • Pi.single j (1:ℝ)) : ℝ × (Fin n → ℝ))) := by
        fun_prop
      exact hg.cont.comp hcomp.continuousOn (fun w hw => hmem w hw)


def GShift (G : ℝ → (Fin n → ℝ) → ℝ) (i j : Fin n) : Prop :=
  ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b → ∀ ε : ℝ, 0 < ε → ε ≤ b i →
    G z (b - ε • (Pi.single i 1 - Pi.single j 1)) ≤ G z b

lemma f_shift (M : Model n) (hM : M.Standing) (i j : Fin n) (hij : j < i) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.k) (hG : GShift (M.g (t-1)) i j) : GShift (M.f t) i j := by
  intro z hz B hB ε hε hεB
  have hS := stageOf M hM t ht
  have hgG := g_good M hM (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
  have hne : i ≠ j := hij.ne'
  have hBk : ∀ k, 0 ≤ B k := fun k => hB k
  set d : Fin n → ℝ := Pi.single i 1 - Pi.single j 1 with hd
  have hdi : d i = 1 := by simp [d, hne]
  have hdj : d j = -1 := by simp [d, hne.symm]
  have hdk : ∀ k, k ≠ i → k ≠ j → d k = 0 := by intro k h1 h2; simp [d, h1, h2]
  have hdsum : ∑ k, d k = 0 := by simp [d, Finset.sum_sub_distrib]
  have hB'k : ∀ k, (B - ε • d) k = B k - ε * d k := fun k => by simp
  have hB' : 0 ≤ B - ε • d := by
    intro k; rw [Pi.zero_apply, hB'k]
    by_cases h1 : k = i
    · subst h1; rw [hdi]; linarith
    · by_cases h2 : k = j
      · subst h2; rw [hdj]; nlinarith [hBk k]
      · rw [hdk k h1 h2]; simpa using hB k
  obtain ⟨u, ⟨hu0, huB, hus⟩, hEq, hmin⟩ :=
    stage_min M t (M.g (t-1)) hS hgG (z, B) ⟨hz, hB⟩
  simp only at hEq hmin huB hus
  have hu0k : ∀ k, 0 ≤ u k := fun k => hu0 k
  set δ := min ε (u i) with hδ
  have hδ0 : 0 ≤ δ := le_min hε.le (hu0k i)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδu : δ ≤ u i := min_le_right _ _
  have hu'k : ∀ k, (u - δ • d) k = u k - δ * d k := fun k => by simp
  have hfeas : u - δ • d ∈ feasible z (B - ε • d) := by
    refine ⟨fun k => ?_, fun k => ?_, ?_⟩
    · rw [Pi.zero_apply, hu'k]
      by_cases h1 : k = i
      · subst h1; rw [hdi]; linarith
      · by_cases h2 : k = j
        · subst h2; rw [hdj]; nlinarith [hu0k k]
        · rw [hdk k h1 h2]; simpa using hu0 k
    · rw [hu'k, hB'k]
      by_cases h1 : k = i
      · subst h1; rw [hdi]
        rcases le_total ε (u k) with h | h
        · rw [hδ, min_eq_left h]; linarith [huB k]
        · rw [hδ, min_eq_right h]; linarith
      · by_cases h2 : k = j
        · subst h2; rw [hdj]; linarith [huB k]
        · rw [hdk k h1 h2]; simpa using huB k
    · have : ∀ k, (B - ε • d) k - (u - δ • d) k = (B k - u k) - (ε - δ) * d k := fun k => by
        rw [hB'k, hu'k]; ring
      rw [Finset.sum_congr rfl (fun k _ => this k),
        Finset.sum_sub_distrib (f := fun k => B k - u k), ← Finset.mul_sum, hdsum, mul_zero, sub_zero]
      exact hus
  have hsum' : ∑ k, ((B - ε • d) k - (u - δ • d) k) = ∑ k, (B k - u k) := by
    have : ∀ k, (B - ε • d) k - (u - δ • d) k = (B k - u k) - (ε - δ) * d k := fun k => by
      rw [hB'k, hu'k]; ring
    rw [Finset.sum_congr rfl (fun k _ => this k),
      Finset.sum_sub_distrib (f := fun k => B k - u k), ← Finset.mul_sum, hdsum, mul_zero, sub_zero]
  have hw0 : 0 ≤ z - ∑ k, (B k - u k) := by linarith
  have hobj : M.obj t (M.g (t-1)) z (B - ε • d) (u - δ • d) ≤ M.obj t (M.g (t-1)) z B u := by
    unfold Model.obj
    rw [hsum']
    have hp : M.p t ⬝ᵥ (u - δ • d) = M.p t ⬝ᵥ u - δ * (M.p t i - M.p t j) := by
      simp only [d, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
    have hpm : M.p t j ≤ M.p t i := hM.p_mono t ht hij.le
    have ha : M.a t • (u - δ • d) = M.a t • u - (M.a t * δ) • d := by
      rw [smul_sub, smul_smul]
    have hgle : M.g (t-1) (z - ∑ k, (B k - u k)) (M.a t • (u - δ • d)) ≤
        M.g (t-1) (z - ∑ k, (B k - u k)) (M.a t • u) := by
      rw [ha]
      rcases (mul_nonneg hS.a0 hδ0).lt_or_eq with hpos | hzero
      · apply hG _ hw0 _ (fun k => by
          simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu0k k))
          _ hpos
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hδu hS.a0
      · rw [← hzero, zero_smul, sub_zero]
    rw [hp]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.2 hpm)]
  have hbdd := (image_compact M t (M.g (t-1)) hS hgG (z, B - ε • d) ⟨hz, hB'⟩).bddBelow
  calc M.f t z (B - ε • d) ≤ M.obj t (M.g (t-1)) z (B - ε • d) (u - δ • d) :=
        csInf_le hbdd ⟨u - δ • d, hfeas, rfl⟩
    _ ≤ M.obj t (M.g (t-1)) z B u := hobj
    _ = M.f t z B := hEq.symm

lemma g_shift_all (M : Model n) (hM : M.Standing) (i j : Fin n) (hij : j < i) :
    ∀ t, t ≤ M.k → GShift (M.g t) i j := by
  intro t
  induction t with
  | zero =>
    intro _ z hz b hb ε hε hεb
    have : ∑ k, (b - ε • (Pi.single i (1:ℝ) - Pi.single j 1) : Fin n → ℝ) k = ∑ k, b k := by
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum]
    show M.v₁ z + M.v₂ (z - ∑ k, (b - ε • (Pi.single i (1:ℝ) - Pi.single j 1) : Fin n → ℝ) k) ≤
      M.v₁ z + M.v₂ (z - ∑ k, b k)
    rw [this]
  | succ t ih =>
    intro ht
    have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
    have hF := f_shift M hM i j hij (t+1) ht' (ih (by omega))
    have hfG := f_good M hM (t+1) ht'
    have := hM.μ_prob _ ht'
    intro z hz b hb ε hε hεb
    have hbk : ∀ k, 0 ≤ b k := fun k => hb k
    have hb' : 0 ≤ b - ε • (Pi.single i (1:ℝ) - Pi.single j 1) := by
      intro k
      simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h1 : k = i
      · subst h1; simp [hij.ne']; linarith
      · by_cases h2 : k = j
        · subst h2; simp [h1]; linarith [hbk k]
        · simp [h1, h2]; exact hbk k
    have hgdef : ∀ b0 : Fin n → ℝ, M.g (t+1) z b0 = ∫ x, M.f (t+1) z (b0 + x) ∂(M.μ (t+1)) := by
      intro b0; unfold Model.f; rw [Nat.add_sub_cancel]; rfl
    rw [hgdef, hgdef]
    apply integral_mono_ae
      (int_shift (M.f (t+1)) hfG (M.μ (t+1)) (hM.μ_nonneg _ ht') (hM.μ_mean _ ht') z hz _ hb')
      (int_shift (M.f (t+1)) hfG (M.μ (t+1)) (hM.μ_nonneg _ ht') (hM.μ_mean _ ht') z hz _ hb)
    filter_upwards [hM.μ_nonneg _ ht'] with x hx
    have e : b - ε • (Pi.single i (1:ℝ) - Pi.single j 1) + x =
        (b + x) - ε • (Pi.single i (1:ℝ) - Pi.single j 1) := by abel
    rw [e]
    exact hF z hz (b + x) (add_nonneg hb hx) ε hε (by have := hx i; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; linarith)

theorem lemma_3_core {n : ℕ} (M : Model n) (hM : M.Standing) (i j : Fin n) (hij : j < i)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ t ∈ Finset.Icc 1 M.k, ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B → ε ≤ B i →
      M.f t z (B - ε • (Pi.single i 1 - Pi.single j 1)) ≤ M.f t z B) ∧
    (∀ t ≤ M.k, ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b → ε ≤ b i →
      M.g t z (b - ε • (Pi.single i 1 - Pi.single j 1)) ≤ M.g t z b) := by
  refine ⟨fun t ht z hz B hB hεB => ?_, fun t ht z hz b hb hεb => ?_⟩
  · exact f_shift M hM i j hij t ht (g_shift_all M hM i j hij (t-1)
      (by have := (Finset.mem_Icc.1 ht).2; omega)) z hz B hB ε hε hεB
  · exact g_shift_all M hM i j hij t ht z hz b hb ε hε hεb


lemma single_diff_apply (v : Fin n → ℝ) (c : ℝ) (i j : Fin n) (hne : i ≠ j) (k : Fin n) :
    (v - c • (Pi.single i (1:ℝ) - Pi.single j 1) : Fin n → ℝ) k =
      if k = i then v k - c else if k = j then v k + c else v k := by
  by_cases h1 : k = i
  · subst h1; simp [hne]
  · by_cases h2 : k = j
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma exchange_min (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : (Fin n → ℝ) → ℝ) (hF : ContinuousOn F K) (B : Fin n → ℝ)
    (hex : ∀ u ∈ K, ∀ j i : Fin n, u j < B j → j < i → u i ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ u - δ • (Pi.single i 1 - Pi.single j 1) ∈ K ∧
        F (u - δ • (Pi.single i 1 - Pi.single j 1)) ≤ F u) :
    ∃ u ∈ K, (∀ v ∈ K, F u ≤ F v) ∧ ∀ j i : Fin n, u j < B j → j < i → u i = 0 := by
  obtain ⟨u0, hu0, hmin0⟩ := hK.exists_isMinOn hne hF
  set Opt := K ∩ F ⁻¹' Set.Iic (F u0) with hOpt
  have hOc : IsCompact Opt := hK.of_isClosed_subset
    (hF.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic) Set.inter_subset_left
  have hOne : Opt.Nonempty := ⟨u0, hu0, Set.mem_preimage.2 (Set.mem_Iic.2 le_rfl)⟩
  let Φ : (Fin n → ℝ) → ℝ := fun u => ∑ k, (k.val : ℝ) * u k
  have hΦ : Continuous Φ := continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)
  obtain ⟨u, ⟨huK, huF⟩, huΦ⟩ := hOc.exists_isMinOn hOne hΦ.continuousOn
  have huF' : F u ≤ F u0 := huF
  refine ⟨u, huK, fun v hv => le_trans huF' (hmin0 hv), fun j i hj hji => ?_⟩
  by_contra hne'
  obtain ⟨δ, hδ, hK', hF'⟩ := hex u huK j i hj hji hne'
  have hmem : u - δ • (Pi.single i 1 - Pi.single j 1) ∈ Opt :=
    ⟨hK', Set.mem_preimage.2 (Set.mem_Iic.2 (le_trans hF' huF'))⟩
  have hle : Φ u ≤ Φ (u - δ • (Pi.single i 1 - Pi.single j 1)) := huΦ hmem
  have hcalc : Φ (u - δ • (Pi.single i 1 - Pi.single j 1)) = Φ u - δ * ((i.val : ℝ) - j.val) := by
    simp only [Φ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    have h1 : ∑ k : Fin n, (k.val : ℝ) * (δ * (Pi.single i (1:ℝ) : Fin n → ℝ) k) = δ * i.val := by
      simp [Pi.single_apply, mul_comm]
    have h2 : ∑ k : Fin n, (k.val : ℝ) * (δ * (Pi.single j (1:ℝ) : Fin n → ℝ) k) = δ * j.val := by
      simp [Pi.single_apply, mul_comm]
    rw [h1, h2]
  have hij' : (j.val : ℝ) < i.val := by exact_mod_cast hji
  rw [hcalc] at hle
  nlinarith [mul_pos hδ (sub_pos.2 hij')]

lemma pg_exchange (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (i j : Fin n) (hij : j < i) (hG : GShift (M.g (t-1)) i j) (w : ℝ) (hw : 0 ≤ w)
    (u : Fin n → ℝ) (hu : 0 ≤ u) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u i) :
    M.p t ⬝ᵥ (u - δ • (Pi.single i 1 - Pi.single j 1)) +
        M.g (t-1) w (M.a t • (u - δ • (Pi.single i 1 - Pi.single j 1))) ≤
      M.p t ⬝ᵥ u + M.g (t-1) w (M.a t • u) := by
  have hS := stageOf M hM t ht
  have hp : M.p t ⬝ᵥ (u - δ • (Pi.single i 1 - Pi.single j 1)) =
      M.p t ⬝ᵥ u - δ * (M.p t i - M.p t j) := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
  have hpm : M.p t j ≤ M.p t i := hM.p_mono t ht hij.le
  have ha : M.a t • (u - δ • (Pi.single i (1:ℝ) - Pi.single j 1)) =
      M.a t • u - (M.a t * δ) • (Pi.single i (1:ℝ) - Pi.single j 1) := by
    rw [smul_sub, smul_smul]
  have hgle : M.g (t-1) w (M.a t • (u - δ • (Pi.single i 1 - Pi.single j 1))) ≤
      M.g (t-1) w (M.a t • u) := by
    rw [ha]
    rcases (mul_nonneg hS.a0 hδ0).lt_or_eq with hpos | hzero
    · apply hG _ hw _ (fun k => by
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu k))
        _ hpos
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hδu hS.a0
    · rw [← hzero, zero_smul, sub_zero]
  rw [hp]
  nlinarith [mul_nonneg hδ0 (sub_nonneg.2 hpm)]

lemma feasible_compact (z : ℝ) (B : Fin n → ℝ) : IsCompact (feasible z B) := by
  apply (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := B)).of_isClosed_subset
  · show IsClosed ({u : Fin n → ℝ | 0 ≤ u} ∩ ({u | u ≤ B} ∩ {u | ∑ j, (B j - u j) ≤ z}))
    exact (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const))
  · rintro u ⟨h0, h1, _⟩; exact ⟨h0, h1⟩

lemma obj_contOn (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (hS : GoodStage M t) (hG : GoodG G)
    (z : ℝ) (B : Fin n → ℝ) :
    ContinuousOn (fun u => M.obj t G z B u) (feasible z B) := by
  unfold Model.obj
  have hdot : Continuous (fun u : Fin n → ℝ => M.p t ⬝ᵥ u) := by
    unfold dotProduct; fun_prop
  have hw : Continuous (fun u : Fin n → ℝ => z - ∑ j, (B j - u j)) := by fun_prop
  apply ContinuousOn.add
  · exact hdot.continuousOn.add (hS.hcont.comp hw.continuousOn (fun u hu => by
      simp only [Set.mem_Ici]; linarith [hu.2.2]))
  · have hc : Continuous (fun u : Fin n → ℝ => ((z - ∑ j, (B j - u j)), M.a t • u)) :=
      hw.prodMk (continuous_const_smul (M.a t))
    exact hG.cont.comp hc.continuousOn (fun u hu => ⟨by simp only [Set.mem_Ici]; linarith [hu.2.2],
      fun k => by simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu.1 k)⟩)

theorem corollary_1_core {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B) :
    ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
      ∀ j i : Fin n, u j < B j → j < i → u i = 0 := by
  have hS := stageOf M hM t ht
  have hgG := g_good M hM (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
  obtain ⟨u0, hu0f, hEq0, hmin0⟩ := stage_min M t (M.g (t-1)) hS hgG (z, B) ⟨hz, hB⟩
  simp only at hEq0 hmin0 hu0f
  obtain ⟨u, huK, humin, hP⟩ := exchange_min (feasible z B) (feasible_compact z B) ⟨u0, hu0f⟩ _
    (obj_contOn M t (M.g (t-1)) hS hgG z B) B (by
      intro u hu j i hj hji hi
      have hne : i ≠ j := hji.ne'
      have hsh := g_shift_all M hM i j hji (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
      obtain ⟨hu0, huB, hus⟩ := hu
      have hu0k : ∀ k, 0 ≤ u k := fun k => hu0 k
      have hui : 0 < u i := lt_of_le_of_ne (hu0k i) (Ne.symm hi)
      set δ := min (u i) (B j - u j) with hδ
      have hδ0 : 0 < δ := lt_min hui (by linarith)
      have hδu : δ ≤ u i := min_le_left _ _
      have hδB : δ ≤ B j - u j := min_le_right _ _
      have hsum : ∑ k, (B k - (u - δ • (Pi.single i (1:ℝ) - Pi.single j 1) : Fin n → ℝ) k) = ∑ k, (B k - u k) := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have : ∀ k, B k - (u k - δ * ((Pi.single i (1:ℝ) : Fin n → ℝ) k - (Pi.single j (1:ℝ) : Fin n → ℝ) k)) =
            (B k - u k) + δ * ((Pi.single i (1:ℝ) : Fin n → ℝ) k - (Pi.single j (1:ℝ) : Fin n → ℝ) k) := fun k => by ring
        rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib]
        simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
      refine ⟨δ, hδ0, ⟨fun k => ?_, fun k => ?_, ?_⟩, ?_⟩
      · rw [Pi.zero_apply, single_diff_apply u δ i j hne k]
        split_ifs with h1 h2
        · subst h1; linarith
        · linarith [hu0k k]
        · exact hu0k k
      · rw [single_diff_apply u δ i j hne k]
        split_ifs with h1 h2
        · subst h1; linarith [huB k, hu0k k]
        · subst h2; linarith
        · exact huB k
      · rw [hsum]; exact hus
      · unfold Model.obj
        rw [hsum]
        have hw0 : 0 ≤ z - ∑ k, (B k - u k) := by linarith
        have := pg_exchange M hM t ht i j hji hsh _ hw0 u hu0 δ hδ0.le hδu
        linarith)
  refine ⟨u, huK, ?_, hP⟩
  show M.stage t (M.g (t-1)) z B = _
  rw [hEq0]
  exact le_antisymm (hmin0 u huK) (humin u0 hu0f)


lemma Sw_nonempty (z w : ℝ) (B : Fin n → ℝ) (hB : 0 ≤ B)
    (hw : w ∈ Set.Icc (max (z - ∑ j, B j) 0) z) :
    ({u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} : Set (Fin n → ℝ)).Nonempty := by
  obtain ⟨hw1, hw2⟩ := hw
  have hBk : ∀ k, 0 ≤ B k := fun k => hB k
  have hSB : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun j _ => hBk j
  have hzw : z - w ≤ ∑ j, B j := by linarith [le_max_left (z - ∑ j, B j) 0]
  have hzw0 : 0 ≤ z - w := by linarith
  set r := (z - w) / ∑ j, B j with hr
  have hr0 : 0 ≤ r := div_nonneg hzw0 hSB
  have hr1 : r ≤ 1 := by
    rcases hSB.lt_or_eq with h | h
    · rw [hr, div_le_one h]; exact hzw
    · rw [hr, ← h, div_zero]; exact zero_le_one
  refine ⟨B - r • B, fun k => ?_, fun k => ?_, ?_⟩
  · simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; nlinarith [hBk k]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; nlinarith [hBk k]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel, ← Finset.mul_sum]
    rcases hSB.lt_or_eq with h | h
    · rw [hr, div_mul_cancel₀ _ h.ne']
    · rw [← h, mul_zero]; linarith

theorem eq_6_core {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B) :
    M.f t z B = sInf ((fun w => M.fw t w z B) '' Set.Icc (max (z - ∑ j, B j) 0) z) ∧
    ∃ w ∈ Set.Icc (max (z - ∑ j, B j) 0) z, M.fw t w z B = M.f t z B := by
  have hS := stageOf M hM t ht
  have hgG := g_good M hM (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
  obtain ⟨u0, hu0f, hEq0, hmin0⟩ := stage_min M t (M.g (t-1)) hS hgG (z, B) ⟨hz, hB⟩
  simp only at hEq0 hmin0 hu0f
  have hf : M.f t z B = M.obj t (M.g (t-1)) z B u0 := hEq0
  have hlow : ∀ w, 0 ≤ w → ∀ u ∈ ({u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} : Set (Fin n → ℝ)),
      M.f t z B - M.h t w ≤ M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u) := by
    intro w hw u hu
    obtain ⟨hu0, huB, hus⟩ := (hu : 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w)
    have hfeas : u ∈ feasible z B := ⟨hu0, huB, by rw [hus]; linarith⟩
    have := hmin0 u hfeas
    have hobj : M.obj t (M.g (t-1)) z B u = M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u) + M.h t w := by
      simp only [Model.obj, hus, sub_sub_cancel]; ring
    rw [hf]; linarith
  have hge : ∀ w ∈ Set.Icc (max (z - ∑ j, B j) 0) z, M.f t z B ≤ M.fw t w z B := by
    intro w hw
    have hw0 : 0 ≤ w := le_trans (le_max_right _ _) hw.1
    unfold Model.fw
    have := le_csInf ((Sw_nonempty z w B hB hw).image _)
      (by rintro _ ⟨u, hu, rfl⟩; exact hlow w hw0 u hu)
    linarith
  set w0 := z - ∑ j, (B j - u0 j) with hw0def
  have hsum0 : 0 ≤ ∑ j, (B j - u0 j) := Finset.sum_nonneg fun j _ => by linarith [hu0f.2.1 j]
  have hsumB : ∑ j, (B j - u0 j) ≤ ∑ j, B j :=
    Finset.sum_le_sum fun j _ => by linarith [hu0f.1 j, show (0 : Fin n → ℝ) j = 0 from rfl]
  have hw0 : w0 ∈ Set.Icc (max (z - ∑ j, B j) 0) z :=
    ⟨max_le (by linarith) (by linarith [hu0f.2.2]), by linarith⟩
  have hfw0 : M.fw t w0 z B = M.f t z B := by
    apply le_antisymm _ (hge w0 hw0)
    unfold Model.fw
    have hu0S : u0 ∈ ({u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w0} : Set (Fin n → ℝ)) :=
      ⟨hu0f.1, hu0f.2.1, by rw [hw0def]; ring⟩
    have hbdd : BddBelow ((fun u => M.p t ⬝ᵥ u + M.g (t - 1) w0 (M.a t • u)) ''
        ({u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w0} : Set (Fin n → ℝ))) := by
      refine ⟨M.f t z B - M.h t w0, ?_⟩
      rintro _ ⟨u, hu, rfl⟩; exact hlow w0 (le_trans (le_max_right _ _) hw0.1) u hu
    have := csInf_le hbdd ⟨u0, hu0S, rfl⟩
    have hobj : M.obj t (M.g (t-1)) z B u0 = M.p t ⬝ᵥ u0 + M.g (t - 1) w0 (M.a t • u0) + M.h t w0 := by
      simp only [Model.obj, hw0def]; ring
    rw [hf]; linarith
  refine ⟨le_antisymm ?_ ?_, w0, hw0, hfw0⟩
  · exact le_csInf ⟨_, w0, hw0, rfl⟩ (by rintro _ ⟨w, hw, rfl⟩; exact hge w hw)
  · calc sInf ((fun w => M.fw t w z B) '' Set.Icc (max (z - ∑ j, B j) 0) z) ≤ M.fw t w0 z B :=
          csInf_le ⟨M.f t z B, by rintro _ ⟨w, hw, rfl⟩; exact hge w hw⟩ ⟨w0, hw0, rfl⟩
      _ = M.f t z B := hfw0

lemma tail_ite (B : Fin n → ℝ) (k : Fin n) :
    tailSum B k = ∑ m, if k ≤ m then B m else 0 := by
  rw [tailSum, ← Finset.sum_filter]
  congr 1; ext m; simp

lemma uVec_of_P (B u : Fin n → ℝ) (s : ℝ) (hu0 : 0 ≤ u) (huB : u ≤ B)
    (hus : ∑ j, (B j - u j) = s)
    (hP : ∀ j i : Fin n, u j < B j → j < i → u i = 0) : uVec s B = u := by
  funext k
  have hu0k : ∀ m, 0 ≤ u m := fun m => hu0 m
  set L := ∑ m, if m < k then B m - u m else 0 with hL
  set R := ∑ m, if k < m then u m else 0 with hR
  have hiden : tailSum B k - s = u k + R - L := by
    rw [tail_ite, ← hus, ← Finset.sum_sub_distrib]
    have : ∀ m, ((if k ≤ m then B m else 0) - (B m - u m)) =
        (if m = k then u k else 0) + (if k < m then u m else 0) - (if m < k then B m - u m else 0) := by
      intro m
      rcases lt_trichotomy m k with h | h | h
      · simp [h, not_le.2 h, h.ne, not_lt.2 h.le]
      · subst h; simp
      · simp [h, h.le, h.ne', not_lt.2 h.le]
    rw [Finset.sum_congr rfl (fun m _ => this m), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [hL, hR]
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun m _ => by split_ifs <;> linarith [huB m]
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun m _ => by split_ifs <;> linarith [hu0k m]
  unfold uVec
  rw [hiden]
  rcases hL0.lt_or_eq with hLpos | hLz
  · obtain ⟨m, hmk, hm⟩ : ∃ m, m < k ∧ u m < B m := by
      by_contra hcon
      push_neg at hcon
      have : L = 0 := Finset.sum_eq_zero fun m _ => by
        split_ifs with h
        · linarith [hcon m h, huB m]
        · rfl
      linarith
    have huk : u k = 0 := hP m k hm hmk
    have hRz : R = 0 := Finset.sum_eq_zero fun i _ => by
      split_ifs with h
      · exact hP m i hm (hmk.trans h)
      · rfl
    rw [huk, hRz, max_eq_right (by linarith)]
    exact min_eq_left ((hu0k k).trans (huB k))
  · rw [← hLz, sub_zero]
    rcases (huB k).lt_or_eq with hlt | heq
    · have hRz : R = 0 := Finset.sum_eq_zero fun i _ => by
        split_ifs with h
        · exact hP k i hlt h
        · rfl
      rw [hRz, add_zero, max_eq_left (hu0k k), min_eq_left (huB k)]
    · rw [heq, min_eq_right]; exact le_max_of_le_left (by linarith)

theorem lemma_4_core {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B)
    (w : ℝ) (hw : w ∈ Set.Icc (max (z - ∑ j, B j) 0) z) :
    uVec (z - w) B ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} ∧
    ∀ u ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w},
      M.p t ⬝ᵥ uVec (z - w) B + M.g (t - 1) w (M.a t • uVec (z - w) B) ≤
        M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u) := by
  have hS := stageOf M hM t ht
  have hgG := g_good M hM (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
  have hw0 : 0 ≤ w := le_trans (le_max_right _ _) hw.1
  set K : Set (Fin n → ℝ) := {u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} with hKdef
  have hKc : IsCompact K := by
    apply (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := B)).of_isClosed_subset
    · show IsClosed ({u : Fin n → ℝ | 0 ≤ u} ∩ ({u | u ≤ B} ∩ {u | ∑ j, (B j - u j) = z - w}))
      exact (isClosed_le continuous_const continuous_id).inter
        ((isClosed_le continuous_id continuous_const).inter
          (isClosed_eq (by fun_prop) continuous_const))
    · rintro u ⟨h0, h1, _⟩; exact ⟨h0, h1⟩
  have hFc : ContinuousOn (fun u => M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u)) K := by
    have hdot : Continuous (fun u : Fin n → ℝ => M.p t ⬝ᵥ u) := by
      unfold dotProduct; fun_prop
    have hc : Continuous (fun u : Fin n → ℝ => (w, M.a t • u)) :=
      continuous_const.prodMk (continuous_const_smul (M.a t))
    exact hdot.continuousOn.add (hgG.cont.comp hc.continuousOn (fun u hu => ⟨hw0,
      fun k => by simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hS.a0 (hu.1 k)⟩))
  obtain ⟨u, huK, humin, hP⟩ := exchange_min K hKc (Sw_nonempty z w B hB hw) _ hFc B (by
      intro u hu j i hj hji hi
      have hne : i ≠ j := hji.ne'
      have hsh := g_shift_all M hM i j hji (t-1) (by have := (Finset.mem_Icc.1 ht).2; omega)
      obtain ⟨hu0, huB, hus⟩ := hu
      have hu0k : ∀ k, 0 ≤ u k := fun k => hu0 k
      have hui : 0 < u i := lt_of_le_of_ne (hu0k i) (Ne.symm hi)
      set δ := min (u i) (B j - u j) with hδ
      have hδ0 : 0 < δ := lt_min hui (by linarith)
      have hδu : δ ≤ u i := min_le_left _ _
      have hδB : δ ≤ B j - u j := min_le_right _ _
      have hsum : ∑ k, (B k - (u - δ • (Pi.single i (1:ℝ) - Pi.single j 1) : Fin n → ℝ) k) = ∑ k, (B k - u k) := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have : ∀ k, B k - (u k - δ * ((Pi.single i (1:ℝ) : Fin n → ℝ) k - (Pi.single j (1:ℝ) : Fin n → ℝ) k)) =
            (B k - u k) + δ * ((Pi.single i (1:ℝ) : Fin n → ℝ) k - (Pi.single j (1:ℝ) : Fin n → ℝ) k) := fun k => by ring
        rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib]
        simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
      refine ⟨δ, hδ0, ⟨fun k => ?_, fun k => ?_, ?_⟩, ?_⟩
      · rw [Pi.zero_apply, single_diff_apply u δ i j hne k]
        split_ifs with h1 h2
        · subst h1; linarith
        · linarith [hu0k k]
        · exact hu0k k
      · rw [single_diff_apply u δ i j hne k]
        split_ifs with h1 h2
        · subst h1; linarith [huB k, hu0k k]
        · subst h2; linarith
        · exact huB k
      · rw [hsum]; exact hus
      · exact pg_exchange M hM t ht i j hji hsh w hw0 u hu0 δ hδ0.le hδu)
  have heq : uVec (z - w) B = u := uVec_of_P B u (z - w) huK.1 huK.2.1 huK.2.2 hP
  rw [heq]
  exact ⟨huK, humin⟩

end TopkisRation.Levels

open TopkisRation.Levels


theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B)
    (w : ℝ) (hw : w ∈ Set.Icc (max (z - ∑ j, B j) 0) z) :
    uVec (z - w) B ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} ∧
    ∀ u ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w},
      M.p t ⬝ᵥ uVec (z - w) B + M.g (t - 1) w (M.a t • uVec (z - w) B) ≤
        M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u) := by
  exact lemma_4_core M hM t ht z hz B hB w hw
