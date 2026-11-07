-- Prove2me | solution 1 for ProjNewton.Superlinear.unit_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:11:41.546547+00:00
-- url     : https://prove2.me/submissions/2f1bde9c-ec3b-40ef-8565-5079aee50a3b

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear
open Matrix Filter Topology Finset

variable {n : ℕ}

lemma arc_apply (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (a : ℝ) (i : Fin n) :
    arc f D x a i = max 0 (x i - a * dir f D x i) := by
  simp [arc, posPart]

lemma herm_symm {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) (i j : Fin n) :
    D i j = D j i := by
  have := hD.apply i j
  simpa using this.symm

lemma mulVec_restrict {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) {i : Fin n} (hi : i ∉ I) :
    (D *ᵥ g) i = (D *ᵥ (fun j => if j ∈ I then 0 else g j)) i := by
  simp only [mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ I
  · have h1 : D i j = 0 := by
      rw [herm_symm hD]
      exact hdiag j hj i (fun h => hi (h ▸ hj))
    simp [h1, hj]
  · simp [hj]

lemma mulVec_diag {D : Matrix (Fin n) (Fin n) ℝ} {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) {i : Fin n} (hi : i ∈ I) :
    (D *ᵥ g) i = D i i * g i := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hdiag i hi j hji, zero_mul]
  · simp

lemma quad_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) :
    ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i =
      star (fun j => if j ∈ I then 0 else g j) ⬝ᵥ (D *ᵥ (fun j => if j ∈ I then 0 else g j)) := by
  rw [dotProduct, ← Finset.sum_compl_add_sum I]
  rw [Finset.sum_eq_zero (s := I) (fun i hi => by simp [hi]), add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_compl] at hi
  rw [mulVec_restrict hD hdiag g hi]
  simp [hi]

lemma quad_nonneg {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) :
    0 ≤ ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := by
  rw [quad_eq hD.1 hdiag]
  by_cases h0 : (fun j => if j ∈ I then 0 else g j) = 0
  · rw [h0]; simp
  · exact (hD.dotProduct_mulVec_pos h0).le

lemma quad_pos {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) (h : ∃ i ∉ I, g i ≠ 0) :
    0 < ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := by
  rw [quad_eq hD.1 hdiag]
  apply hD.dotProduct_mulVec_pos
  obtain ⟨i, hi, hgi⟩ := h
  intro h0
  have := congrFun h0 i
  simp [hi] at this
  exact hgi this

lemma quad_le_zero {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) (h : ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i ≤ 0) :
    ∀ i ∉ I, g i = 0 := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.mpr (quad_pos hD hdiag g hc))

lemma mem_Iplus (f : Vec n → ℝ) (x : Vec n) (i : Fin n) :
    i ∈ Iplus f x ↔ x i = 0 ∧ 0 < pd f x i := by
  simp [Iplus]

lemma mem_Ik (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ) (x : Vec n) (i : Fin n) :
    i ∈ Ik f μ ε x ↔ 0 ≤ x i ∧ x i ≤ min ε (w f μ x) ∧ 0 < pd f x i := by
  simp [Ik]

lemma w_eq_zero_of_critical {f : Vec n → ℝ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {x : Vec n}
    (hc : IsCritical f x) : w f μ x = 0 := by
  unfold w
  rw [norm_eq_zero, sub_eq_zero]
  ext i
  simp only [posPart, PiLp.toLp_apply, PiLp.sub_apply]
  obtain ⟨hx, hg, hpos⟩ := hc
  have hxi : 0 ≤ x i := hx i
  rcases hxi.lt_or_eq with h | h
  · rw [hpos i h]; simp [h.le]
  · rw [← h]
    have : 0 ≤ μ i * pd f x i := mul_nonneg (hμ i).le (hg i)
    simp [this]

lemma critical_iff {f : Vec n → ℝ} {x : Vec n} (hx : x ∈ orthant n) :
    IsCritical f x ↔ ∀ i ∉ Iplus f x, pd f x i = 0 := by
  constructor
  · rintro ⟨_, hg, hpos⟩ i hi
    rw [mem_Iplus] at hi
    rcases (hx i).lt_or_eq with h | h
    · exact hpos i h
    · have : ¬ 0 < pd f x i := fun h' => hi ⟨h.symm, h'⟩
      linarith [hg i]
  · intro h
    refine ⟨hx, fun i => ?_, fun i hi => ?_⟩
    · by_cases hi : i ∈ Iplus f x
      · exact ((mem_Iplus f x i).1 hi).2.le
      · exact (h i hi).ge
    · apply h i
      rw [mem_Iplus]
      exact fun h' => (ne_of_gt hi) h'.1

lemma Ik_eq_Iplus_of_critical {f : Vec n → ℝ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {ε : ℝ}
    (hε : 0 < ε) {x : Vec n} (hc : IsCritical f x) : Ik f μ ε x = Iplus f x := by
  ext i
  rw [mem_Ik, mem_Iplus, w_eq_zero_of_critical hμ hc, min_eq_right hε.le]
  have := hc.1 i
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨le_antisymm h2 h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1.ge, h1.le, h3⟩

lemma fderiv_eq_sum (f : Vec n → ℝ) (x v : Vec n) :
    fderiv ℝ f x v = ∑ i, pd f x i * v i := by
  have : fderiv ℝ f x v = inner ℝ (gradient f x) v := by
    simp [gradient]
  rw [this, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, pd, mul_comm]

/-- general form of the Armijo right-side positivity for arbitrary `a > 0`. -/
lemma rhs_general {f : Vec n → ℝ} {μ : Fin n → ℝ} {ε : ℝ} (hμ : ∀ i, 0 < μ i) (hε : 0 < ε)
    {x : Vec n} (hx : x ∈ orthant n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Ik f μ ε x)) {a : ℝ} (ha : 0 < a) :
    0 ≤ armijoRHS f μ ε D x a ∧ (0 < armijoRHS f μ ε D x a ↔ ¬ IsCritical f x) := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  have hS := quad_nonneg hD hdiag g
  have hp : ∀ i ∈ I, 0 < dir f D x i := by
    intro i hi
    simp only [dir]
    rw [mulVec_diag hdiag _ hi]
    exact mul_pos hD.diag_pos ((mem_Ik f μ ε x i).1 hi).2.2
  have hterm : ∀ i ∈ I, 0 ≤ pd f x i * (x i - arc f D x a i) := by
    intro i hi
    apply mul_nonneg ((mem_Ik f μ ε x i).1 hi).2.2.le
    rw [arc_apply]
    have := hp i hi
    have := hx i
    apply sub_nonneg.mpr
    apply max_le this
    nlinarith
  have hT : 0 ≤ ∑ i ∈ I, pd f x i * (x i - arc f D x a i) := Finset.sum_nonneg hterm
  have hSdef : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := rfl
  have hnn : 0 ≤ armijoRHS f μ ε D x a := by
    unfold armijoRHS
    rw [← hI, hSdef]
    have := mul_nonneg ha.le hS
    linarith
  refine ⟨hnn, ?_, ?_⟩
  · intro hpos hc
    have hIx : ∀ i ∈ I, x i = 0 := by
      intro i hi
      have h := (mem_Ik f μ ε x i).1 hi
      rw [w_eq_zero_of_critical hμ hc, min_eq_right hε.le] at h
      exact le_antisymm h.2.1 h.1
    have hgI : ∀ i ∉ I, pd f x i = 0 := by
      intro i hi
      rw [hI, Ik_eq_Iplus_of_critical hμ hε hc] at hi
      exact (critical_iff hx).1 hc i hi
    have h1 : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hgI i (Finset.mem_compl.1 hi), zero_mul])
    have h2 : ∑ i ∈ I, pd f x i * (x i - arc f D x a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [arc_apply, hIx i hi]
      have := hp i hi
      have : max 0 (0 - a * dir f D x i) = 0 := by
        apply max_eq_left; nlinarith
      rw [this]; ring
    unfold armijoRHS at hpos
    rw [← hI, h1, h2] at hpos
    simp at hpos
  · intro hnc
    by_contra hle
    have h0 : armijoRHS f μ ε D x a = 0 := le_antisymm (not_lt.1 hle) hnn
    unfold armijoRHS at h0
    rw [← hI, hSdef] at h0
    have hS0 : ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i = 0 := by
      have := mul_nonneg ha.le hS
      have : a * ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hT0 : ∑ i ∈ I, pd f x i * (x i - arc f D x a i) = 0 := by
      rw [hS0, mul_zero, zero_add] at h0; exact h0
    have hgI : ∀ i ∉ I, pd f x i = 0 := quad_le_zero hD hdiag g hS0.le
    have hIx : ∀ i ∈ I, x i = 0 := by
      intro i hi
      have ht := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hT0 i hi
      have hgpos := ((mem_Ik f μ ε x i).1 hi).2.2
      rcases mul_eq_zero.1 ht with h | h
      · linarith
      · rw [arc_apply] at h
        have := hp i hi
        have hxi := hx i
        by_contra hne
        have hxpos : 0 < x i := lt_of_le_of_ne hxi (Ne.symm hne)
        have : max 0 (x i - a * dir f D x i) < x i := by
          apply max_lt hxpos; nlinarith
        linarith
    apply hnc
    refine ⟨hx, fun i => ?_, fun i hi => ?_⟩
    · by_cases hi : i ∈ I
      · exact ((mem_Ik f μ ε x i).1 hi).2.2.le
      · exact (hgI i hi).ge
    · apply hgI i
      intro hiI
      rw [hIx i hiI] at hi
      exact lt_irrefl _ hi


/-- The direction along which the projected arc is linear for small stepsizes. -/
noncomputable def dvec (x : Vec n) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 < x i then p i else min 0 (p i)

lemma arc_eventually (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) {x : Vec n}
    (hx : x ∈ orthant n) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), arc f D x a = x - a • WithLp.toLp 2 (dvec x (dir f D x)) := by
  have : ∀ᶠ a in 𝓝[>] (0:ℝ), ∀ i, arc f D x a i = x i - a * dvec x (dir f D x) i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hxi : 0 < x i
    · have ht : Tendsto (fun a : ℝ => x i - a * dir f D x i) (𝓝 0) (𝓝 (x i)) := by
        have : Tendsto (fun a : ℝ => x i - a * dir f D x i) (𝓝 0)
            (𝓝 (x i - 0 * dir f D x i)) := by
          exact tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds)
        simpa using this
      have hev := ht.eventually (lt_mem_nhds hxi)
      have hev' : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < x i - a * dir f D x i := nhdsWithin_le_nhds hev
      filter_upwards [hev'] with a ha
      rw [arc_apply, dvec, if_pos hxi, max_eq_right]
      exact ha.le
    · have hx0 : x i = 0 := le_antisymm (not_lt.1 hxi) (hx i)
      filter_upwards [self_mem_nhdsWithin] with a ha
      have ha' : 0 < a := ha
      rw [arc_apply, dvec, if_neg hxi, hx0]
      rcases le_or_gt 0 (dir f D x i) with hp | hp
      · rw [min_eq_left hp, max_eq_left]
        · ring
        · nlinarith
      · rw [min_eq_right hp.le, max_eq_right]
        nlinarith
  filter_upwards [this] with a ha
  ext i
  rw [ha i]
  simp

lemma tendsto_descent {f : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x)
    (d : Fin n → ℝ) :
    Tendsto (fun a : ℝ => (f x - f (x - a • WithLp.toLp 2 d)) / a) (𝓝[>] 0)
      (𝓝 (∑ i, pd f x i * d i)) := by
  set v : Vec n := WithLp.toLp 2 d
  have hline : HasDerivAt (fun a : ℝ => x - a • v) (-v) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_sub x
    simpa using this
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x - (0:ℝ) • v) := by
    simpa using hf.hasFDerivAt
  have hcomp := hf'.comp_hasDerivAt (0:ℝ) hline
  rw [hasDerivAt_iff_tendsto_slope] at hcomp
  have hcomp' := (hcomp.mono_left (nhdsWithin_mono _ (fun a (ha : 0 < a) => ne_of_gt ha))).neg
  have heq : -(fderiv ℝ f x (-v)) = ∑ i, pd f x i * d i := by
    rw [map_neg, neg_neg, fderiv_eq_sum]
  rw [heq] at hcomp'
  apply hcomp'.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  simp only [slope, Function.comp, vsub_eq_sub, smul_eq_mul, zero_smul, sub_zero]
  rw [div_eq_inv_mul]; ring


lemma dir_pos_of_mem {f : Vec n → ℝ} {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef)
    {I : Finset (Fin n)} (hdiag : DiagonalWrt D I) {x : Vec n} {i : Fin n} (hi : i ∈ I)
    (hg : 0 < pd f x i) : 0 < dir f D x i := by
  simp only [dir]
  rw [mulVec_diag hdiag _ hi]
  exact mul_pos hD.diag_pos hg

lemma prop1a {f : Vec n → ℝ} {x : Vec n} (hx : x ∈ orthant n)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Iplus f x))
    (hc : IsCritical f x) : ∀ a : ℝ, 0 ≤ a → arc f D x a = x := by
  intro a ha
  ext i
  rw [arc_apply]
  by_cases hi : i ∈ Iplus f x
  · have hmem := (mem_Iplus f x i).1 hi
    have hp := dir_pos_of_mem hD hdiag hi hmem.2
    rw [hmem.1]
    apply max_eq_left
    nlinarith
  · have : dir f D x i = 0 := by
      simp only [dir]
      rw [mulVec_restrict hD.1 hdiag _ hi]
      have h0 : (fun j => if j ∈ Iplus f x then 0 else pd f x j) = 0 := by
        funext j
        split_ifs with hj
        · rfl
        · exact (critical_iff hx).1 hc j hj
      rw [h0, mulVec_zero]
      rfl
    rw [this, mul_zero, sub_zero, max_eq_right (hx i)]

lemma prop1_core {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) (x : Vec n) (hx : x ∈ orthant n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Iplus f x)) :
    (IsCritical f x ↔ ∀ a : ℝ, 0 ≤ a → arc f D x a = x) ∧
    (¬ IsCritical f x → ∃ abar : ℝ, 0 < abar ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) abar, f (arc f D x a) < f x) := by
  have hdiff : DifferentiableAt ℝ f x := (hf.differentiable one_ne_zero) x
  set I := Iplus f x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  refine ⟨⟨fun hc => prop1a hx hD hdiag hc, fun h => ?_⟩, fun hnc => ?_⟩
  · rw [critical_iff hx]
    apply quad_le_zero hD hdiag g
    apply Finset.sum_nonpos
    intro i hi
    rw [Finset.mem_compl] at hi
    have h1 := congrArg (fun y : Vec n => y i) (h 1 zero_le_one)
    simp only [arc_apply, one_mul] at h1
    have hdir : (D *ᵥ g) i = dir f D x i := rfl
    rw [hdir]
    rcases (hx i).lt_or_eq with hxi | hxi
    · have : x i - dir f D x i = x i := by
        rcases max_choice 0 (x i - dir f D x i) with h' | h' <;> rw [h'] at h1
        · linarith
        · exact h1
      have hp0 : dir f D x i = 0 := by linarith
      rw [hp0, mul_zero]
    · have hp : 0 ≤ dir f D x i := by
        have := le_max_right 0 (x i - dir f D x i)
        rw [h1] at this
        linarith
      have hgi : g i ≤ 0 := by
        by_contra hgi
        exact hi ((mem_Iplus f x i).2 ⟨hxi.symm, lt_of_not_ge hgi⟩)
      nlinarith
  · have hS : 0 < ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := by
      apply quad_pos hD hdiag g
      by_contra h
      push Not at h
      exact hnc ((critical_iff hx).2 h)
    set d := dvec x (dir f D x) with hd
    have hgd : ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i ≤ ∑ i, pd f x i * d i := by
      rw [← Finset.sum_compl_add_sum I (fun i => pd f x i * d i)]
      have h1 : ∑ i ∈ I, pd f x i * d i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hmem := (mem_Iplus f x i).1 hi
        have hp := dir_pos_of_mem hD hdiag hi hmem.2
        have : d i = 0 := by
          rw [hd, dvec, if_neg (by rw [hmem.1]; exact lt_irrefl 0), min_eq_left hp.le]
        rw [this, mul_zero]
      rw [h1, add_zero]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_compl] at hi
      have hdir : (D *ᵥ g) i = dir f D x i := rfl
      rw [hdir, hd, dvec]
      split_ifs with hxi
      · exact le_rfl
      · have hx0 : x i = 0 := le_antisymm (not_lt.1 hxi) (hx i)
        have hgi : g i ≤ 0 := by
          by_contra hgi
          exact hi ((mem_Iplus f x i).2 ⟨hx0, lt_of_not_ge hgi⟩)
        exact mul_le_mul_of_nonpos_left (min_le_right _ _) hgi
    have hlim := tendsto_descent hdiff d
    have hev1 := hlim.eventually (lt_mem_nhds (lt_of_lt_of_le hS hgd))
    have hev := hev1.and ((arc_eventually f D hx).and self_mem_nhdsWithin)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
    refine ⟨u, hu, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hsub ha
    have ha0 : 0 < a := h3
    rw [h2]
    have := (div_pos_iff_of_pos_right ha0).1 h1
    linarith

lemma arc_mem_orthant (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (a : ℝ) :
    arc f D x a ∈ orthant n := by
  intro i
  rw [arc_apply]
  exact le_max_left _ _

lemma wd_core {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) :
    (∀ (x : Vec n), x ∈ orthant n →
      ∀ (D : Matrix (Fin n) (Fin n) ℝ), D.PosDef →
      DiagonalWrt D (Ik f μ ε x) →
      (¬ IsCritical f x → ∃ m₀ : ℕ, ∀ m ≥ m₀, Armijo f μ ε β σ D x m) ∧
      (IsCritical f x → Armijo f μ ε β σ D x 0 ∧ arc f D x 1 = x)) ∧
    (∀ (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n),
      IsRun f μ ε β σ D x → AdmissibleScaling f μ ε D x →
      ∀ k, x k ∈ orthant n ∧
        (¬ IsCritical f (x k) → f (x (k + 1)) < f (x k)) ∧
        (IsCritical f (x k) → x (k + 1) = x k)) := by
  have hμ := hpar.mu_pos
  have hε := hpar.eps_pos
  have hσ0 : 0 < σ := hpar.sigma_mem.1
  have hσ1 : σ < 1 / 2 := hpar.sigma_mem.2
  have hβ0 : 0 < β := hpar.beta_mem.1
  have hβ1 : β < 1 := hpar.beta_mem.2
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have part1 : ∀ (x : Vec n), x ∈ orthant n →
      ∀ (D : Matrix (Fin n) (Fin n) ℝ), D.PosDef →
      DiagonalWrt D (Ik f μ ε x) →
      (¬ IsCritical f x → ∃ m₀ : ℕ, ∀ m ≥ m₀, Armijo f μ ε β σ D x m) ∧
      (IsCritical f x → Armijo f μ ε β σ D x 0 ∧ arc f D x 1 = x) := by
    intro x hx D hD hdiag
    constructor
    · intro hnc
      set I := Ik f μ ε x with hI
      set d := dvec x (dir f D x) with hd
      set R := ∑ i ∈ Iᶜ, pd f x i * dir f D x i + ∑ i ∈ I, pd f x i * d i with hR
      have hRHS : ∀ᶠ a in 𝓝[>] (0:ℝ), arc f D x a = x - a • WithLp.toLp 2 d ∧
          armijoRHS f μ ε D x a = a * R ∧ 0 < a := by
        filter_upwards [arc_eventually f D hx, self_mem_nhdsWithin] with a ha ha0
        refine ⟨ha, ?_, ha0⟩
        unfold armijoRHS
        rw [← hI, ha]
        have hc : ∀ i, x i - (x - a • WithLp.toLp 2 d : Vec n) i = a * d i := by
          intro i; rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]; ring
        rw [← hd]
        simp_rw [hc]
        rw [hR, mul_add]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hRpos : 0 < R := by
        obtain ⟨a, ha1, ha2, ha3⟩ := hRHS.exists
        have := (rhs_general hμ hε hx hD hdiag ha3).2.2 hnc
        rw [ha2] at this
        exact (pos_iff_pos_of_mul_pos this).1 ha3
      have hgd : R ≤ ∑ i, pd f x i * d i := by
        rw [← Finset.sum_compl_add_sum I (fun i => pd f x i * d i), hR]
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_compl] at hi
        rw [hd, dvec]
        split_ifs with hxi
        · exact le_rfl
        · have hx0 : x i = 0 := le_antisymm (not_lt.1 hxi) (hx i)
          have hgi : pd f x i ≤ 0 := by
            by_contra hgi
            apply hi
            rw [mem_Ik, hx0]
            exact ⟨le_rfl, le_min hε.le (norm_nonneg _), lt_of_not_ge hgi⟩
          exact mul_le_mul_of_nonpos_left (min_le_right _ _) hgi
      have hlt : σ * R < ∑ i, pd f x i * d i := by nlinarith
      have hlim := tendsto_descent (hdiff x) d
      have hev1 := hlim.eventually (lt_mem_nhds hlt)
      have hP : ∀ᶠ a in 𝓝[>] (0:ℝ),
          σ * armijoRHS f μ ε D x a ≤ f x - f (arc f D x a) := by
        filter_upwards [hev1, hRHS] with a h1 h2
        obtain ⟨h2a, h2b, h2c⟩ := h2
        rw [h2b, h2a]
        rw [lt_div_iff₀ h2c] at h1
        linarith
      have htend : Tendsto (fun m : ℕ => β ^ m) atTop (𝓝[>] (0:ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1,
          Filter.Eventually.of_forall (fun m => pow_pos hβ0 m)⟩
      obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 (htend.eventually hP)
      exact ⟨m₀, fun m hm => hm₀ m hm⟩
    · intro hc
      have hIk := Ik_eq_Iplus_of_critical hμ hε hc
      have hdiag' : DiagonalWrt D (Iplus f x) := hIk ▸ hdiag
      have harc1 := prop1a hx hD hdiag' hc 1 zero_le_one
      refine ⟨?_, harc1⟩
      unfold Armijo
      rw [pow_zero, harc1, sub_self]
      have h := (rhs_general hμ hε hx hD hdiag one_pos).2
      have hle : armijoRHS f μ ε D x 1 ≤ 0 := not_lt.1 (fun hp => h.1 hp hc)
      nlinarith
  refine ⟨part1, ?_⟩
  intro D x hrun hadm k
  have hxk : ∀ k, x k ∈ orthant n := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ k =>
      obtain ⟨m, -, -, hx⟩ := hrun.2 k
      rw [hx]
      exact arc_mem_orthant _ _ _ _
  obtain ⟨m, hA, hmin, hnext⟩ := hrun.2 k
  refine ⟨hxk k, fun hnc => ?_, fun hc => ?_⟩
  · have hpos := (rhs_general hμ hε (hxk k) (hadm k).1 (hadm k).2 (pow_pos hβ0 m)).2.2 hnc
    unfold Armijo at hA
    rw [hnext]
    nlinarith [mul_pos hσ0 hpos]
  · have h0 := (part1 _ (hxk k) _ (hadm k).1 (hadm k).2).2 hc
    have hm0 : m = 0 := by
      by_contra hm
      exact hmin 0 (Nat.pos_of_ne_zero hm) h0.1
    rw [hnext, hm0, pow_zero, h0.2]



lemma dot_symm {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) (u v : Fin n → ℝ) :
    u ⬝ᵥ (D *ᵥ v) = v ⬝ᵥ (D *ᵥ u) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [herm_symm hD i j]; ring

lemma cs_form {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hnn : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ (D *ᵥ u)) {c : ℝ} (hc : 0 < c)
    (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c * (u ⬝ᵥ u)) (z : Fin n → ℝ) :
    (D *ᵥ z) ⬝ᵥ (D *ᵥ z) ≤ c * (z ⬝ᵥ (D *ᵥ z)) := by
  set v := D *ᵥ z
  set A := z ⬝ᵥ (D *ᵥ z)
  set B := v ⬝ᵥ v
  set C := v ⬝ᵥ (D *ᵥ v)
  have hzv : z ⬝ᵥ (D *ᵥ v) = B := by
    rw [dot_symm hD]
  have hexp : ∀ t : ℝ, (z + t • v) ⬝ᵥ (D *ᵥ (z + t • v)) = A + 2 * t * B + t ^ 2 * C := by
    intro t
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [hzv]
    have : v ⬝ᵥ (D *ᵥ z) = B := rfl
    rw [this]; ring
  have h1 := hnn (z + (-1 / c) • v)
  rw [hexp] at h1
  have hC : C ≤ c * B := hup v
  have : A + 2 * (-1 / c) * B + (-1 / c) ^ 2 * (c * B) ≥ 0 := by
    have : (-1 / c) ^ 2 * C ≤ (-1 / c) ^ 2 * (c * B) :=
      mul_le_mul_of_nonneg_left hC (sq_nonneg _)
    linarith
  have heq : A + 2 * (-1 / c) * B + (-1 / c) ^ 2 * (c * B) = A - B / c := by
    field_simp; ring
  rw [heq] at this
  have : B / c ≤ A := by linarith
  rw [div_le_iff₀ hc] at this
  linarith


lemma descent {f : Vec n → ℝ} (hf : Differentiable ℝ f) {S : Set (Vec n)} (hS : Convex ℝ S)
    {L : NNReal} (hL : LipschitzOnWith L (gradient f) S) {y z : Vec n} (hy : y ∈ S) (hz : z ∈ S) :
    f z ≤ f y + ∑ i, pd f y i * (z - y) i + L * ‖z - y‖ ^ 2 := by
  set v := z - y
  set φ : ℝ → ℝ := fun t => f (y + t • v)
  have hderiv : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ f (y + t • v) v) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => y + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    exact (hf (y + t • v)).hasFDerivAt.comp_hasDerivAt t hl
  have hcont : ContinuousOn φ (Set.Icc 0 1) :=
    (continuous_iff_continuousAt.2 (fun t => (hderiv t).continuousAt)).continuousOn
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope φ (fun t => fderiv ℝ f (y + t • v) v)
    zero_lt_one hcont (fun t _ => hderiv t)
  have h1 : φ 1 = f z := by simp [φ, v]
  have h0 : φ 0 = f y := by simp [φ]
  rw [h1, h0, sub_zero, div_one] at hceq
  have hmem : y + c • v ∈ S := by
    have := hS.add_smul_sub_mem hy hz ⟨hc.1.le, hc.2.le⟩
    simpa [v] using this
  have hfd : ∀ u : Vec n, fderiv ℝ f u v = inner ℝ (gradient f u) v := by
    intro u; simp [gradient]
  rw [hfd] at hceq
  have hlin : ∑ i, pd f y i * v i = inner ℝ (gradient f y) v := by
    rw [← fderiv_eq_sum, hfd]
  rw [hlin]
  have hdiff : inner ℝ (gradient f (y + c • v)) v - inner ℝ (gradient f y) v ≤ L * ‖v‖ ^ 2 := by
    rw [← inner_sub_left]
    calc inner ℝ (gradient f (y + c • v) - gradient f y) v
        ≤ ‖gradient f (y + c • v) - gradient f y‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (L * ‖(y + c • v) - y‖) * ‖v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have := hL.dist_le_mul _ hmem _ hy
          simpa [dist_eq_norm] using this
      _ ≤ L * ‖v‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
          have hL0 : (0:ℝ) ≤ L := L.2
          have : c * ‖v‖ ≤ ‖v‖ := by nlinarith [norm_nonneg v, hc.2]
          have := mul_le_mul_of_nonneg_left this hL0
          nlinarith [norm_nonneg v]
  linarith


lemma posdef_nonneg {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (u : Fin n → ℝ) :
    0 ≤ u ⬝ᵥ (D *ᵥ u) := by
  by_cases hu : u = 0
  · rw [hu]; simp
  · have := hD.dotProduct_mulVec_pos hu
    simpa using this.le

lemma diag_le {D : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c * (u ⬝ᵥ u)) (i : Fin n) : D i i ≤ c := by
  have := hup (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using this

lemma diag_ge {D : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hlo : ∀ u : Fin n → ℝ, c * (u ⬝ᵥ u) ≤ u ⬝ᵥ (D *ᵥ u)) (i : Fin n) : c ≤ D i i := by
  have := hlo (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using this

lemma grad_dot (f : Vec n → ℝ) (x : Vec n) :
    (fun i => pd f x i) ⬝ᵥ (fun i => pd f x i) = ‖gradient f x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, pd, sq]

lemma norm_sq_vec (v : Vec n) : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

lemma sub_max_eq_min (x q : ℝ) : x - max 0 (x - q) = min x q := by
  rcases le_total 0 (x - q) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring

lemma armijo_of_small {f : Vec n → ℝ} (hf : Differentiable ℝ f) {μ : Fin n → ℝ} {ε σ : ℝ}
    (hμ : ∀ i, 0 < μ i) (hε : 0 < ε)
    (hσ : σ ≤ 1) {x xbar : Vec n} (hx : x ∈ orthant n) (hxb : ‖x - xbar‖ ≤ 1)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Ik f μ ε x))
    {c2 : ℝ} (hc2 : 0 < c2) (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c2 * (u ⬝ᵥ u))
    {G : ℝ} (hG : ‖gradient f x‖ ≤ G) {εbar : ℝ} (hεbar : εbar ≤ min ε (w f μ x))
    {L : NNReal} (hL : LipschitzOnWith L (gradient f) (Metric.closedBall xbar (1 + c2 * G)))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (haε : a * (c2 * G) ≤ εbar)
    (haL : a * (L * c2) ≤ 1 - σ) :
    σ * armijoRHS f μ ε D x a ≤ f x - f (arc f D x a) := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  set p : Fin n → ℝ := dir f D x with hp
  have hpg : p = D *ᵥ g := rfl
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  have hnn := posdef_nonneg hD
  have hgg : g ⬝ᵥ g ≤ G ^ 2 := by
    rw [hg, grad_dot]; exact pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hpp : p ⬝ᵥ p ≤ (c2 * G) ^ 2 := by
    rw [hpg]
    have h1 := cs_form hD.1 hnn hc2 hup g
    have h2 := hup g
    have h3 : c2 * (g ⬝ᵥ (D *ᵥ g)) ≤ c2 * (c2 * (g ⬝ᵥ g)) := mul_le_mul_of_nonneg_left h2 hc2.le
    have h4 : c2 * (c2 * (g ⬝ᵥ g)) ≤ c2 * (c2 * G ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgg hc2.le) hc2.le
    nlinarith
  have hpi : ∀ i, |p i| ≤ c2 * G := by
    intro i
    have : p i ^ 2 ≤ p ⬝ᵥ p := by
      have := Finset.single_le_sum (f := fun j => p j * p j) (fun j _ => mul_self_nonneg (p j))
        (Finset.mem_univ i)
      simpa [dotProduct, sq] using this
    have hK : 0 ≤ c2 * G := mul_nonneg hc2.le hG0
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  set e : Fin n → ℝ := fun i => x i - arc f D x a i with he
  have he_min : ∀ i, e i = min (x i) (a * p i) := by
    intro i; simp only [he]; rw [arc_apply, sub_max_eq_min]
  have he_sq : ∀ i, e i ^ 2 ≤ a ^ 2 * p i ^ 2 := by
    intro i
    rw [he_min]
    have hxi := hx i
    rcases le_total (x i) (a * p i) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  -- Key 1
  have hlin : armijoRHS f μ ε D x a ≤ ∑ i, g i * e i := by
    unfold armijoRHS
    rw [← hI, ← Finset.sum_compl_add_sum I (fun i => g i * e i)]
    apply add_le_add _ le_rfl
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_compl] at hi
    show a * (g i * p i) ≤ g i * e i
    rw [he_min]
    rcases le_total (a * p i) (x i) with h | h
    · rw [min_eq_right h]; ring_nf; exact le_rfl
    · rw [min_eq_left h]
      rcases le_or_gt (g i) 0 with hgi | hgi
      · nlinarith
      · exfalso
        apply hi
        rw [mem_Ik]
        refine ⟨hx i, ?_, hgi⟩
        have := hpi i
        have : a * p i ≤ a * (c2 * G) := by
          have := le_abs_self (p i)
          nlinarith
        linarith
  -- Key 2
  have hsq : ∑ i, e i ^ 2 ≤ a * c2 * armijoRHS f μ ε D x a := by
    unfold armijoRHS
    rw [← hI, ← Finset.sum_compl_add_sum I (fun i => e i ^ 2)]
    set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j
    have hS : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = gJ ⬝ᵥ (D *ᵥ gJ) := by
      have := quad_eq hD.1 hdiag g
      simp only [star_trivial] at this
      exact this
    have hA : ∑ i ∈ Iᶜ, e i ^ 2 ≤ a ^ 2 * (c2 * (gJ ⬝ᵥ (D *ᵥ gJ))) := by
      calc ∑ i ∈ Iᶜ, e i ^ 2 ≤ ∑ i ∈ Iᶜ, a ^ 2 * p i ^ 2 := Finset.sum_le_sum (fun i _ => he_sq i)
        _ = a ^ 2 * ∑ i ∈ Iᶜ, (D *ᵥ gJ) i ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_compl] at hi
            rw [hpg, mulVec_restrict hD.1 hdiag g hi]
        _ ≤ a ^ 2 * ((D *ᵥ gJ) ⬝ᵥ (D *ᵥ gJ)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
            have : (D *ᵥ gJ) ⬝ᵥ (D *ᵥ gJ) = ∑ i, (D *ᵥ gJ) i ^ 2 := by
              simp [dotProduct, sq]
            rw [this]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => sq_nonneg _)
        _ ≤ a ^ 2 * (c2 * (gJ ⬝ᵥ (D *ᵥ gJ))) :=
            mul_le_mul_of_nonneg_left (cs_form hD.1 hnn hc2 hup gJ) (sq_nonneg a)
    have hB : ∑ i ∈ I, e i ^ 2 ≤ a * c2 * ∑ i ∈ I, pd f x i * (x i - arc f D x a i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hgi := ((mem_Ik f μ ε x i).1 hi).2.2
      have hpi' : p i = D i i * g i := by rw [hpg, mulVec_diag hdiag g hi]
      have hDii := diag_le hup i
      have hDpos : 0 < D i i := hD.diag_pos
      show e i ^ 2 ≤ a * c2 * (g i * e i)
      have he0 : 0 ≤ e i := by
        rw [he_min]; exact le_min (hx i) (by rw [hpi']; positivity)
      have hle : e i ≤ a * p i := by rw [he_min]; exact min_le_right _ _
      have h1 : e i ^ 2 ≤ e i * (a * p i) := by nlinarith
      rw [hpi'] at h1
      have h2 : e i * (a * (D i i * g i)) ≤ e i * (a * (c2 * g i)) := by
        apply mul_le_mul_of_nonneg_left _ he0
        apply mul_le_mul_of_nonneg_left _ ha.le
        exact mul_le_mul_of_nonneg_right hDii hgi.le
      nlinarith
    rw [hS]
    nlinarith
  -- Key 3: membership in the ball
  have hnorm : ‖arc f D x a - x‖ ^ 2 = ∑ i, e i ^ 2 := by
    rw [norm_sq_vec]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, PiLp.sub_apply]
    ring
  have hsmall : ‖arc f D x a - x‖ ≤ c2 * G := by
    have h1 : ∑ i, e i ^ 2 ≤ (c2 * G) ^ 2 := by
      calc ∑ i, e i ^ 2 ≤ ∑ i, a ^ 2 * p i ^ 2 := Finset.sum_le_sum (fun i _ => he_sq i)
        _ = a ^ 2 * (p ⬝ᵥ p) := by rw [dotProduct, Finset.mul_sum]; simp [sq]
        _ ≤ 1 * (p ⬝ᵥ p) := by
            have hpp0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg (fun j _ => mul_self_nonneg (p j))
            apply mul_le_mul_of_nonneg_right _ hpp0
            nlinarith
        _ ≤ (c2 * G) ^ 2 := by linarith
    rw [← hnorm] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc2.le hG0) two_ne_zero).1 h1
  have hxmem : x ∈ Metric.closedBall xbar (1 + c2 * G) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    nlinarith [mul_nonneg hc2.le hG0]
  have harcmem : arc f D x a ∈ Metric.closedBall xbar (1 + c2 * G) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖arc f D x a - xbar‖ = ‖(arc f D x a - x) + (x - xbar)‖ := by congr 1; abel
      _ ≤ ‖arc f D x a - x‖ + ‖x - xbar‖ := norm_add_le _ _
      _ ≤ 1 + c2 * G := by linarith
  -- Key 4: descent
  have hdes := descent hf (convex_closedBall xbar (1 + c2 * G)) hL hxmem harcmem
  have hlin2 : ∑ i, pd f x i * (arc f D x a - x) i = -∑ i, g i * e i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, hg, PiLp.sub_apply]
    ring
  rw [hlin2, hnorm] at hdes
  have hRHS0 := (rhs_general hμ hε hx hD hdiag ha).1
  have hL0 : (0:ℝ) ≤ L := L.2
  have h5 : (L:ℝ) * ∑ i, e i ^ 2 ≤ L * (a * c2 * armijoRHS f μ ε D x a) :=
    mul_le_mul_of_nonneg_left hsq hL0
  have h6 : σ * armijoRHS f μ ε D x a ≤ (1 - a * (L * c2)) * armijoRHS f μ ε D x a :=
    mul_le_mul_of_nonneg_right (by linarith) hRHS0
  nlinarith


lemma grad_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have h1 : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv one_ne_zero
  exact (InnerProductSpace.toDual ℝ (Vec n)).symm.continuous.comp h1

lemma pd_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun x => pd f x i) := by
  have := grad_continuous hf
  unfold pd
  fun_prop

lemma w_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) :
    Continuous (fun x => w f μ x) := by
  have := pd_continuous hf
  unfold w posPart
  fun_prop

lemma crit_of_w_zero {f : Vec n → ℝ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {x : Vec n}
    (hx : x ∈ orthant n) (hw : w f μ x = 0) : IsCritical f x := by
  unfold w at hw
  rw [norm_eq_zero] at hw
  have hc : ∀ i, min (x i) (μ i * pd f x i) = 0 := by
    intro i
    have := congrArg (fun y : Vec n => y i) hw
    simp only [posPart, PiLp.sub_apply, PiLp.toLp_apply, PiLp.zero_apply] at this
    rw [← sub_max_eq_min]; exact this
  have hmain : ∀ i, 0 ≤ pd f x i ∧ (0 < x i → pd f x i = 0) := by
    intro i
    have h := hc i
    have hμi := hμ i
    rcases le_total (x i) (μ i * pd f x i) with h' | h'
    · rw [min_eq_left h'] at h
      refine ⟨?_, fun hp => absurd h (ne_of_gt hp)⟩
      by_contra hneg; push Not at hneg
      nlinarith
    · rw [min_eq_right h'] at h
      have : pd f x i = 0 := by
        rcases mul_eq_zero.1 h with h1 | h1
        · linarith
        · exact h1
      exact ⟨this.ge, fun _ => this⟩
  exact ⟨hx, fun i => (hmain i).1, fun i hi => (hmain i).2 hi⟩

lemma rhs_mono {f : Vec n → ℝ} {μ : Fin n → ℝ} {ε : ℝ}
    {x : Vec n} (hx : x ∈ orthant n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Ik f μ ε x)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    armijoRHS f μ ε D x a ≤ armijoRHS f μ ε D x b := by
  unfold armijoRHS
  have hS := quad_nonneg hD hdiag (fun i => pd f x i)
  have hS' : 0 ≤ ∑ i ∈ (Ik f μ ε x)ᶜ, pd f x i * dir f D x i := hS
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hab hS'
  · apply Finset.sum_le_sum
    intro i hi
    have hg := ((mem_Ik f μ ε x i).1 hi).2.2
    have hp := dir_pos_of_mem hD hdiag hi hg
    apply mul_le_mul_of_nonneg_left _ hg.le
    rw [arc_apply, arc_apply, sub_max_eq_min, sub_max_eq_min]
    apply min_le_min le_rfl
    nlinarith

lemma orthant_closed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {x : Vec n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [this]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (by fun_prop)


/-- The continuous merit function used to pass to the limit. -/
noncomputable def Psi (f : Vec n → ℝ) (c : ℝ) (i : Fin n) (y : Vec n) : ℝ :=
  min (c * pd f y i ^ 2)
    (max 0 (pd f y i) * min (y i) (c * max 0 (pd f y i)) + min 0 (pd f y i) ^ 2)

lemma Psi_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ) (i : Fin n) :
    Continuous (Psi f c i) := by
  have := pd_continuous hf i
  unfold Psi
  fun_prop

lemma Psi_nonneg {f : Vec n → ℝ} {c : ℝ} (hc : 0 ≤ c) (i : Fin n) {y : Vec n}
    (hy : y ∈ orthant n) : 0 ≤ Psi f c i y := by
  unfold Psi
  apply le_min (mul_nonneg hc (sq_nonneg _))
  have h1 : 0 ≤ max 0 (pd f y i) := le_max_left _ _
  have h2 : 0 ≤ min (y i) (c * max 0 (pd f y i)) := le_min (hy i) (mul_nonneg hc h1)
  nlinarith [sq_nonneg (min 0 (pd f y i))]

lemma crit_of_Psi {f : Vec n → ℝ} {c : ℝ} (hc : 0 < c) {y : Vec n} (hy : y ∈ orthant n)
    (h : ∀ i, Psi f c i y = 0) : IsCritical f y := by
  have hmain : ∀ i, 0 ≤ pd f y i ∧ (0 < y i → pd f y i = 0) := by
    intro i
    have hi := h i
    unfold Psi at hi
    set g := pd f y i
    rcases min_choice (c * g ^ 2) (max 0 g * min (y i) (c * max 0 g) + min 0 g ^ 2) with h' | h'
    · rw [h'] at hi
      have : g = 0 := by
        have : g ^ 2 = 0 := by
          rcases mul_eq_zero.1 hi with h1 | h1
          · linarith
          · exact h1
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      exact ⟨this.ge, fun _ => this⟩
    · rw [h'] at hi
      have h1 : 0 ≤ max 0 g := le_max_left _ _
      have h2 : 0 ≤ min (y i) (c * max 0 g) := le_min (hy i) (mul_nonneg hc.le h1)
      have h3 : 0 ≤ max 0 g * min (y i) (c * max 0 g) := mul_nonneg h1 h2
      have h4 : min 0 g ^ 2 = 0 := by nlinarith [sq_nonneg (min 0 g)]
      have hg0 : 0 ≤ g := by
        have : min 0 g = 0 := pow_eq_zero_iff two_ne_zero |>.1 h4
        rw [← this]; exact min_le_right _ _
      refine ⟨hg0, fun hyi => ?_⟩
      by_contra hne
      have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hne)
      rw [max_eq_right hgpos.le] at h3 hi
      have h5 : g * min (y i) (c * g) = 0 := by nlinarith
      have h6 : 0 < min (y i) (c * g) := lt_min hyi (mul_pos hc hgpos)
      have := mul_pos hgpos h6
      linarith
  exact ⟨hy, fun i => (hmain i).1, fun i hi => (hmain i).2 hi⟩

lemma Psi_le_rhs {f : Vec n → ℝ} {μ : Fin n → ℝ} {ε : ℝ} {x : Vec n} (hx : x ∈ orthant n)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Ik f μ ε x))
    {c1 : ℝ} (hc1 : 0 < c1) (hlo : ∀ u : Fin n → ℝ, c1 * (u ⬝ᵥ u) ≤ u ⬝ᵥ (D *ᵥ u))
    {a : ℝ} (ha : 0 < a) (i : Fin n) :
    Psi f (a * c1) i x ≤ armijoRHS f μ ε D x a := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun j => pd f x j with hg
  set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j
  have hS : ∑ j ∈ Iᶜ, pd f x j * dir f D x j = gJ ⬝ᵥ (D *ᵥ gJ) := by
    have := quad_eq hD.1 hdiag g
    simp only [star_trivial] at this
    exact this
  have hT : ∀ j ∈ I, 0 ≤ pd f x j * (x j - arc f D x a j) := by
    intro j hj
    have hgj := ((mem_Ik f μ ε x j).1 hj).2.2
    have hp := dir_pos_of_mem hD hdiag hj hgj
    apply mul_nonneg hgj.le
    rw [arc_apply, sub_max_eq_min]
    exact le_min (hx j) (by positivity)
  have hTs : 0 ≤ ∑ j ∈ I, pd f x j * (x j - arc f D x a j) := Finset.sum_nonneg hT
  have hSnn : 0 ≤ gJ ⬝ᵥ (D *ᵥ gJ) := posdef_nonneg hD gJ
  unfold armijoRHS
  rw [← hI, hS]
  by_cases hi : i ∈ I
  · have hgi := ((mem_Ik f μ ε x i).1 hi).2.2
    have hpi : dir f D x i = D i i * pd f x i := by
      simp only [dir]; rw [mulVec_diag hdiag _ hi]
    have hDii := diag_ge hlo i
    have hle : Psi f (a * c1) i x ≤ pd f x i * (x i - arc f D x a i) := by
      unfold Psi
      apply le_trans (min_le_right _ _)
      rw [max_eq_right hgi.le, min_eq_left hgi.le, arc_apply, sub_max_eq_min]
      have : (0:ℝ) ^ 2 = 0 := by norm_num
      rw [this, add_zero]
      apply mul_le_mul_of_nonneg_left _ hgi.le
      apply min_le_min le_rfl
      rw [hpi]
      have := mul_le_mul_of_nonneg_right hDii hgi.le
      nlinarith
    have := Finset.single_le_sum hT hi
    nlinarith [mul_nonneg ha.le hSnn]
  · have hle : Psi f (a * c1) i x ≤ a * c1 * pd f x i ^ 2 := min_le_left _ _
    have h1 : pd f x i ^ 2 ≤ gJ ⬝ᵥ gJ := by
      have := Finset.single_le_sum (f := fun j => gJ j * gJ j) (fun j _ => mul_self_nonneg (gJ j))
        (Finset.mem_univ i)
      have h0 : gJ i = pd f x i := by simp only [gJ, if_neg hi, hg]
      rw [h0] at this
      rw [sq]; exact this
    have h2 := hlo gJ
    have h3 : a * c1 * pd f x i ^ 2 ≤ a * (gJ ⬝ᵥ (D *ᵥ gJ)) := by
      have := mul_le_mul_of_nonneg_left h1 hc1.le
      have := mul_le_mul_of_nonneg_left (le_trans this h2) ha.le
      nlinarith
    linarith


lemma prop2_core {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) (hA : AssumptionA f)
    (μ : Fin n → ℝ) (ε β σ : ℝ) (hpar : Params μ ε β σ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n)
    (hrun : IsRun f μ ε β σ D x)
    (hadm : AdmissibleScaling f μ ε D x)
    (lam1 lam2 : ℝ) (q₁ q₂ : ℕ)
    (hB : AssumptionB f μ D x lam1 lam2 q₁ q₂) :
    ∀ xbar : Vec n, MapClusterPt xbar atTop x → IsCritical f xbar := by
  intro xbar hcl
  by_contra hnc
  have hμ := hpar.mu_pos
  have hε := hpar.eps_pos
  have hσ0 : 0 < σ := hpar.sigma_mem.1
  have hσ1 : σ < 1 / 2 := hpar.sigma_mem.2
  have hβ0 : 0 < β := hpar.beta_mem.1
  have hβ1 : β < 1 := hpar.beta_mem.2
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hstep := (wd_core hf μ ε β σ hpar).2 D x hrun hadm
  have hxo : ∀ k, x k ∈ orthant n := fun k => (hstep k).1
  have hanti : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hc : IsCritical f (x k)
    · rw [(hstep k).2.2 hc]
    · exact ((hstep k).2.1 hc).le
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have hxbo : xbar ∈ orthant n :=
    orthant_closed.mem_of_tendsto hlim (Eventually.of_forall (fun k => hxo _))
  set wb := w f μ xbar with hwb
  have hwbar : 0 < wb :=
    lt_of_le_of_ne (norm_nonneg _) (fun h => hnc (crit_of_w_zero hμ hxbo h.symm))
  set Gb := ‖gradient f xbar‖ + 1 with hGb
  have hGb1 : 1 ≤ Gb := by rw [hGb]; linarith [norm_nonneg (gradient f xbar)]
  -- eventual neighbourhood facts along the subsequence
  have hev1 : ∀ᶠ k in atTop, ‖x (ψ k) - xbar‖ ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.1 hlim 1 one_pos] with k hk
    rw [← dist_eq_norm]; exact hk.le
  have hwlim : Tendsto (fun k => w f μ (x (ψ k))) atTop (𝓝 wb) :=
    ((w_continuous hf μ).tendsto xbar).comp hlim
  have hev2 : ∀ᶠ k in atTop, wb / 2 ≤ w f μ (x (ψ k)) ∧ w f μ (x (ψ k)) ≤ wb + 1 := by
    filter_upwards [hwlim.eventually (Ioo_mem_nhds (by linarith : wb / 2 < wb)
      (by linarith : wb < wb + 1))] with k hk
    exact ⟨hk.1.le, hk.2.le⟩
  have hglim : Tendsto (fun k => ‖gradient f (x (ψ k))‖) atTop (𝓝 ‖gradient f xbar‖) :=
    ((continuous_norm.comp (grad_continuous hf)).tendsto xbar).comp hlim
  have hev3 : ∀ᶠ k in atTop, ‖gradient f (x (ψ k))‖ ≤ Gb := by
    filter_upwards [hglim.eventually (Iio_mem_nhds (by linarith : ‖gradient f xbar‖ < Gb))]
      with k hk
    exact hk.le
  -- constants
  obtain ⟨hl1, hl2, hBk⟩ := hB
  set c1 := lam1 * (wb / 2) ^ q₁ with hc1
  set c2 := lam2 * (wb + 1) ^ q₂ with hc2
  have hc1p : 0 < c1 := mul_pos hl1 (pow_pos (by linarith) _)
  have hc2p : 0 < c2 := mul_pos hl2 (pow_pos (by linarith) _)
  set εbar := min ε (wb / 2) with hεbar
  have hεbarp : 0 < εbar := lt_min hε (by linarith)
  obtain ⟨L, hL⟩ := hA (Metric.closedBall xbar (1 + c2 * Gb)) Metric.isBounded_closedBall
  have hL0 : (0:ℝ) ≤ L := L.2
  set abar := min 1 (min (εbar / (c2 * Gb)) ((1 - σ) / (L * c2 + 1))) with habar
  have hc2G : 0 < c2 * Gb := mul_pos hc2p (by linarith)
  have hLc : 0 < (L:ℝ) * c2 + 1 := by nlinarith
  have habarp : 0 < abar :=
    lt_min one_pos (lt_min (div_pos hεbarp hc2G) (div_pos (by linarith) hLc))
  have habar1 : abar ≤ 1 := min_le_left _ _
  have habarε : abar * (c2 * Gb) ≤ εbar := by
    have : abar ≤ εbar / (c2 * Gb) := le_trans (min_le_right _ _) (min_le_left _ _)
    rwa [le_div_iff₀ hc2G] at this
  have habarL : abar * (L * c2) ≤ 1 - σ := by
    have : abar ≤ (1 - σ) / (L * c2 + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ hLc] at this
    nlinarith
  -- per-index bounds
  have hbounds : ∀ᶠ k in atTop,
      (∀ u : Fin n → ℝ, c1 * (u ⬝ᵥ u) ≤ u ⬝ᵥ (D (ψ k) *ᵥ u)) ∧
      (∀ u : Fin n → ℝ, u ⬝ᵥ (D (ψ k) *ᵥ u) ≤ c2 * (u ⬝ᵥ u)) ∧
      εbar ≤ min ε (w f μ (x (ψ k))) ∧ ‖x (ψ k) - xbar‖ ≤ 1 ∧
      ‖gradient f (x (ψ k))‖ ≤ Gb := by
    filter_upwards [hev1, hev2, hev3] with k h1 h2 h3
    refine ⟨fun u => ?_, fun u => ?_, min_le_min le_rfl h2.1, h1, h3⟩
    · have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun j _ => mul_self_nonneg (u j))
      have := (hBk (ψ k) u).1
      have hp : (wb / 2) ^ q₁ ≤ w f μ (x (ψ k)) ^ q₁ :=
        pow_le_pow_left₀ (by linarith) h2.1 _
      have : c1 * (u ⬝ᵥ u) ≤ lam1 * w f μ (x (ψ k)) ^ q₁ * (u ⬝ᵥ u) := by
        apply mul_le_mul_of_nonneg_right _ huu
        exact mul_le_mul_of_nonneg_left hp hl1.le
      linarith
    · have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun j _ => mul_self_nonneg (u j))
      have := (hBk (ψ k) u).2
      have hw0 : 0 ≤ w f μ (x (ψ k)) := norm_nonneg _
      have hp : w f μ (x (ψ k)) ^ q₂ ≤ (wb + 1) ^ q₂ := pow_le_pow_left₀ hw0 h2.2 _
      have : lam2 * w f μ (x (ψ k)) ^ q₂ * (u ⬝ᵥ u) ≤ c2 * (u ⬝ᵥ u) := by
        apply mul_le_mul_of_nonneg_right _ huu
        exact mul_le_mul_of_nonneg_left hp hl2.le
      linarith
  -- stepsize lower bound and RHS control
  set a0 := β * abar with ha0
  have ha0p : 0 < a0 := mul_pos hβ0 habarp
  have hrhs : ∀ᶠ k in atTop,
      armijoRHS f μ ε (D (ψ k)) (x (ψ k)) a0 ≤ (f (x (ψ k)) - f (x (ψ k + 1))) / σ := by
    filter_upwards [hbounds] with k hk
    obtain ⟨hlo, hup, hεk, hxk, hGk⟩ := hk
    have harm : ∀ m : ℕ, β ^ m ≤ abar → Armijo f μ ε β σ (D (ψ k)) (x (ψ k)) m := by
      intro m hm
      unfold Armijo
      have hpos : 0 < β ^ m := pow_pos hβ0 m
      exact armijo_of_small hdiff hμ hε (by linarith) (hxo _) hxk (hadm (ψ k)).1
        (hadm (ψ k)).2 hc2p hup hGk hεk hL hpos (le_trans hm habar1)
        (le_trans (mul_le_mul_of_nonneg_right hm hc2G.le) habarε)
        (le_trans (mul_le_mul_of_nonneg_right hm (by positivity)) habarL)
    obtain ⟨m, hAm, hmin, hnext⟩ := hrun.2 (ψ k)
    have hm_ge : a0 ≤ β ^ m := by
      by_contra hlt
      push Not at hlt
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hlt
        have : β * abar < 1 := by nlinarith
        linarith
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have : β ^ m' ≤ abar := by
        rw [pow_succ] at hlt
        have := (mul_lt_mul_iff_of_pos_right hβ0).1 (by linarith : β ^ m' * β < abar * β)
        exact this.le
      exact hmin m' (Nat.lt_succ_self m') (harm m' this)
    have hmono := rhs_mono (hxo (ψ k)) (hadm (ψ k)).1 (hadm (ψ k)).2 ha0p hm_ge
    unfold Armijo at hAm
    rw [← hnext] at hAm
    rw [le_div_iff₀ hσ0]
    nlinarith
  -- the function decrease along the subsequence tends to zero
  have hflim : Tendsto (fun k => f (x (ψ k))) atTop (𝓝 (f xbar)) :=
    ((hdiff.continuous).tendsto xbar).comp hlim
  have hfge : ∀ j, f xbar ≤ f (x j) := by
    intro j
    apply le_of_tendsto hflim
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hanti (le_trans hk (hψ.id_le k))
  have hdec : Tendsto (fun k => (f (x (ψ k)) - f (x (ψ k + 1))) / σ) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => (f (x (ψ k)) - f xbar) / σ) atTop (𝓝 0) := by
      have := (hflim.sub_const (f xbar)).div_const σ
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    · intro k
      apply div_nonneg _ hσ0.le
      have := hanti (Nat.le_succ (ψ k))
      simp only at this
      linarith
    · intro k
      apply div_le_div_of_nonneg_right _ hσ0.le
      linarith [hfge (ψ k + 1)]
  -- pass to the limit in Psi
  have hcrit : ∀ i, Psi f (a0 * c1) i xbar = 0 := by
    intro i
    have hPlim : Tendsto (fun k => Psi f (a0 * c1) i (x (ψ k))) atTop
        (𝓝 (Psi f (a0 * c1) i xbar)) :=
      ((Psi_continuous hf (a0 * c1) i).tendsto xbar).comp hlim
    have hP0 : Tendsto (fun k => Psi f (a0 * c1) i (x (ψ k))) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdec
      · exact Eventually.of_forall (fun k => Psi_nonneg (mul_pos ha0p hc1p).le i (hxo _))
      · filter_upwards [hbounds, hrhs] with k hk hr
        exact le_trans (Psi_le_rhs (hxo _) (hadm (ψ k)).1 (hadm (ψ k)).2 hc1p hk.1 ha0p i) hr
    exact tendsto_nhds_unique hPlim hP0
  exact hnc (crit_of_Psi (mul_pos ha0p hc1p) hxbo hcrit)


lemma grad_apply_eq (f : Vec n → ℝ) (y : Vec n) (i : Fin n) :
    (gradient f y) i = fderiv ℝ f y (EuclideanSpace.single i 1) := by
  rw [fderiv_eq_sum]
  simp [pd, EuclideanSpace.single_apply]

lemma grad_hasFDerivAt {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec n) :
    HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable one_ne_zero
  have : gradient f = fun y => (InnerProductSpace.toDual ℝ (Vec n)).symm (fderiv ℝ f y) := by
    funext y; rfl
  have hd : DifferentiableAt ℝ (gradient f) x := by
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Vec n)).symm.toContinuousLinearEquiv.differentiableAt.comp x
      (h2 x)
  exact hd.hasFDerivAt

lemma pd2_eq {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec n) (i j : Fin n) :
    pd2 f x i j = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable one_ne_zero
  set π : Vec n →L[ℝ] ℝ := EuclideanSpace.proj i
  have hA : HasFDerivAt (fun y => π (gradient f y)) (π.comp (fderiv ℝ (gradient f) x)) x :=
    π.hasFDerivAt.comp x (grad_hasFDerivAt hf x)
  have hfun : (fun y => π (gradient f y)) = fun y => fderiv ℝ f y (EuclideanSpace.single i 1) := by
    funext y
    rw [← grad_apply_eq]
    rfl
  rw [hfun] at hA
  have hB : HasFDerivAt (fun y => fderiv ℝ f y (EuclideanSpace.single i 1))
      ((fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single i 1)) x := by
    have := (h2 x).hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1:ℝ)) x)
    simpa using this
  have := hA.unique hB
  have := congrArg (fun L : Vec n →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at this
  rw [← this]
  rfl

lemma pd2_symm {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec n) (i j : Fin n) :
    pd2 f x i j = pd2 f x j i := by
  rw [pd2_eq hf, pd2_eq hf]
  have hs : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  exact hs _ _


/-- The Hessian matrix. -/
noncomputable def Hess (f : Vec n → ℝ) (x : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => pd2 f x i j

lemma hessForm_eq (f : Vec n → ℝ) (x : Vec n) (z : Fin n → ℝ) :
    hessForm f x z = z ⬝ᵥ (Hess f x *ᵥ z) := by
  simp only [hessForm, dotProduct, mulVec, Hess, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma Hmat_form (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ) (x : Vec n) (z : Fin n → ℝ) :
    z ⬝ᵥ (Hmat f μ ε x *ᵥ z) =
      ∑ i ∈ Ik f μ ε x, pd2 f x i i * z i ^ 2 +
      (fun j => if j ∈ Ik f μ ε x then 0 else z j) ⬝ᵥ
        (Hess f x *ᵥ (fun j => if j ∈ Ik f μ ε x then 0 else z j)) := by
  set I := Ik f μ ε x with hI
  set zJ : Fin n → ℝ := fun j => if j ∈ I then 0 else z j with hzJ
  have key : ∀ i j, z i * (Hmat f μ ε x i j * z j) =
      (if j = i then (if i ∈ I then pd2 f x i i * z i ^ 2 else 0) else 0) +
        zJ i * (pd2 f x i j * zJ j) := by
    intro i j
    by_cases hij : j = i
    · subst hij
      by_cases hi : j ∈ I <;> simp [Hmat, hi, zJ, ← hI] <;> ring
    · have hij' : i ≠ j := Ne.symm hij
      by_cases hi : i ∈ I <;> by_cases hj : j ∈ I <;> simp [Hmat, hi, hj, hij, hij', zJ, ← hI]
  simp only [dotProduct, mulVec, Hess, Finset.mul_sum, key, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma Hmat_symm {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (μ : Fin n → ℝ) (ε : ℝ) (x : Vec n)
    (i j : Fin n) : Hmat f μ ε x i j = Hmat f μ ε x j i := by
  simp only [Hmat]
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : j ≠ i := Ne.symm hij
    by_cases h : i ∈ Ik f μ ε x ∨ j ∈ Ik f μ ε x
    · rw [if_pos ⟨hij, h⟩, if_pos ⟨hji, h.symm⟩]
    · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h (h'.2.symm)), pd2_symm hf]

lemma dot_split (I : Finset (Fin n)) (z : Fin n → ℝ) :
    z ⬝ᵥ z = ∑ i ∈ I, z i ^ 2 +
      (fun j => if j ∈ I then 0 else z j) ⬝ᵥ (fun j => if j ∈ I then 0 else z j) := by
  simp only [dotProduct]
  rw [← Finset.sum_compl_add_sum I, add_comm]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · rw [← Finset.sum_compl_add_sum I]
    rw [Finset.sum_eq_zero (s := I) (fun i hi => by simp [hi]), add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_compl] at hi
    simp [hi]

lemma hess_diag_bounds {f : Vec n → ℝ} {x : Vec n} {m₁ m₂ : ℝ}
    (hb : ∀ z : Fin n → ℝ, m₁ * (z ⬝ᵥ z) ≤ hessForm f x z ∧ hessForm f x z ≤ m₂ * (z ⬝ᵥ z))
    (i : Fin n) : m₁ ≤ pd2 f x i i ∧ pd2 f x i i ≤ m₂ := by
  have h := hb (Pi.single i 1)
  simp only [hessForm_eq] at h
  simpa [dotProduct, mulVec, Hess, Pi.single_apply] using h

lemma Hmat_bounds {f : Vec n → ℝ} (μ : Fin n → ℝ) (ε : ℝ) {x : Vec n} {m₁ m₂ : ℝ}
    (hb : ∀ z : Fin n → ℝ, m₁ * (z ⬝ᵥ z) ≤ hessForm f x z ∧ hessForm f x z ≤ m₂ * (z ⬝ᵥ z))
    (z : Fin n → ℝ) :
    m₁ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Hmat f μ ε x *ᵥ z) ∧ z ⬝ᵥ (Hmat f μ ε x *ᵥ z) ≤ m₂ * (z ⬝ᵥ z) := by
  rw [Hmat_form, dot_split (Ik f μ ε x) z]
  set zJ : Fin n → ℝ := fun j => if j ∈ Ik f μ ε x then 0 else z j
  have hJ := hb zJ
  rw [hessForm_eq] at hJ
  have hsum1 : m₁ * ∑ i ∈ Ik f μ ε x, z i ^ 2 ≤ ∑ i ∈ Ik f μ ε x, pd2 f x i i * z i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hess_diag_bounds hb i).1 (sq_nonneg _))
  have hsum2 : ∑ i ∈ Ik f μ ε x, pd2 f x i i * z i ^ 2 ≤ m₂ * ∑ i ∈ Ik f μ ε x, z i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hess_diag_bounds hb i).2 (sq_nonneg _))
  constructor <;> nlinarith [hJ.1, hJ.2]

lemma Hinv_props {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (μ : Fin n → ℝ) (ε : ℝ) {x : Vec n}
    {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hb : ∀ z : Fin n → ℝ, m₁ * (z ⬝ᵥ z) ≤ hessForm f x z ∧ hessForm f x z ≤ m₂ * (z ⬝ᵥ z)) :
    (Hmat f μ ε x).PosDef ∧ (Hmat f μ ε x)⁻¹.PosDef ∧
      DiagonalWrt (Hmat f μ ε x)⁻¹ (Ik f μ ε x) ∧
      (∀ z : Fin n → ℝ, (1 / m₂) * (z ⬝ᵥ z) ≤ z ⬝ᵥ ((Hmat f μ ε x)⁻¹ *ᵥ z)) ∧
      (∀ z : Fin n → ℝ, z ⬝ᵥ ((Hmat f μ ε x)⁻¹ *ᵥ z) ≤ (1 / m₁) * (z ⬝ᵥ z)) := by
  set H := Hmat f μ ε x with hH
  have hherm : H.IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, hH, Hmat_symm hf μ ε x j i]
  have hbd := Hmat_bounds μ ε hb
  have hpd : H.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hherm
    intro z hz
    simp only [star_trivial]
    have hzz : 0 < z ⬝ᵥ z := by
      rcases Function.ne_iff.1 hz with ⟨i, hi⟩
      have := Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg (z j))
        (Finset.mem_univ i)
      exact lt_of_lt_of_le (mul_self_pos.2 hi) this
    nlinarith [(hbd z).1]
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).1 hpd.isUnit
  have hHinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hinvH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hy : ∀ z, H *ᵥ (H⁻¹ *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hHinv, Matrix.one_mulVec]
  have hnn : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ (H *ᵥ u) := fun u => posdef_nonneg hpd u
  refine ⟨hpd, hpd.inv, ?_, ?_, ?_⟩
  · intro i hi j hji
    have hcol : H *ᵥ (Pi.single i 1) = H i i • Pi.single i 1 := by
      ext k
      simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k = i
      · subst hk; simp
      · rw [if_neg hk]
        simp only [hH, Hmat]
        rw [if_pos ⟨hk, Or.inr hi⟩]
    have hii : 0 < H i i := hpd.diag_pos
    have h1 : H⁻¹ *ᵥ (H *ᵥ Pi.single i 1) = Pi.single i 1 := by
      rw [Matrix.mulVec_mulVec, hinvH, Matrix.one_mulVec]
    rw [hcol, Matrix.mulVec_smul] at h1
    have h2 := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_neg hji] at h2
    have h3 : (H⁻¹ *ᵥ Pi.single i 1) j = H⁻¹ j i := by
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [h3] at h2
    have h4 : H⁻¹ j i = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact h
    rw [herm_symm hpd.inv.1]; exact h4
  · intro z
    set y := H⁻¹ *ᵥ z
    have hz : H *ᵥ y = z := hy z
    have hcs := cs_form hherm hnn hm₂ (fun u => (hbd u).2) y
    rw [hz] at hcs
    show (1 / m₂) * (z ⬝ᵥ z) ≤ z ⬝ᵥ y
    have : z ⬝ᵥ y = y ⬝ᵥ z := dotProduct_comm _ _
    rw [this, div_mul_eq_mul_div, one_mul, div_le_iff₀ hm₂]
    linarith
  · intro z
    set y := H⁻¹ *ᵥ z
    have hz : H *ᵥ y = z := hy z
    have h1 := (hbd y).1
    have h2 : y ⬝ᵥ (H *ᵥ y) = z ⬝ᵥ y := by rw [hz, dotProduct_comm]
    have hamgm : z ⬝ᵥ y ≤ (m₁ / 2) * (y ⬝ᵥ y) + (1 / (2 * m₁)) * (z ⬝ᵥ z) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have : 0 ≤ (m₁ * y i - z i) ^ 2 / (2 * m₁) := by positivity
      have e : (m₁ / 2) * (y i * y i) + (1 / (2 * m₁)) * (z i * z i) - z i * y i =
          (m₁ * y i - z i) ^ 2 / (2 * m₁) := by field_simp; ring
      linarith
    have hyy : y ⬝ᵥ y ≤ (z ⬝ᵥ z) / m₁ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : m₁ * (y ⬝ᵥ y) ≤ (m₁ / 2) * (y ⬝ᵥ y) + (1 / (2 * m₁)) * (z ⬝ᵥ z) := by linarith
      have h3 : (m₁ / 2) * (y ⬝ᵥ y) ≤ (1 / (2 * m₁)) * (z ⬝ᵥ z) := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * m₁)
      field_simp at h4
      nlinarith
    have : (m₁ / 2) * (y ⬝ᵥ y) ≤ (m₁ / 2) * ((z ⬝ᵥ z) / m₁ ^ 2) :=
      mul_le_mul_of_nonneg_left hyy (by positivity)
    have e2 : (m₁ / 2) * ((z ⬝ᵥ z) / m₁ ^ 2) = (1 / (2 * m₁)) * (z ⬝ᵥ z) := by
      field_simp
    have e3 : (1 / (2 * m₁)) * (z ⬝ᵥ z) + (1 / (2 * m₁)) * (z ⬝ᵥ z) = (1 / m₁) * (z ⬝ᵥ z) := by
      field_simp; ring
    linarith


lemma grad_contDiff {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have : gradient f = fun y => (InnerProductSpace.toDual ℝ (Vec n)).symm (fderiv ℝ f y) := by
    funext y; rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Vec n)).symm.contDiff.comp h1

lemma assumptionA_of_C2 {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) : AssumptionA f := by
  intro S hS
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  have hg := grad_contDiff hf
  have hcont : Continuous (fun y => fderiv ℝ (gradient f) y) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec n) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨Real.toNNReal C, ?_⟩
  apply LipschitzOnWith.mono _ hR
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun y _ => (hg.differentiable one_ne_zero) y)
    _ (convex_closedBall 0 R)
  intro y hy
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact le_trans (hC y hy) (le_max_left _ _)

/-- First-order characterization of convexity (one direction). -/
lemma convex_grad_ineq {f : Vec n → ℝ} (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (z y : Vec n) :
    f z + ∑ i, pd f z i * (y - z) i ≤ f y := by
  set d : Fin n → ℝ := fun i => -(y - z) i
  have hlim := tendsto_descent (hf z) d
  have hsum : ∑ i, pd f z i * d i = -∑ i, pd f z i * (y - z) i := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; simp [d]; ring
  rw [hsum] at hlim
  have hbound : ∀ᶠ a in 𝓝[>] (0:ℝ), -(f y - f z) ≤ (f z - f (z - a • WithLp.toLp 2 d)) / a := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with a ha
    have hpt : z - a • WithLp.toLp 2 d = (1 - a) • z + a • y := by
      ext i; simp [d]; ring
    rw [hpt]
    have hc := hconv.2 (Set.mem_univ z) (Set.mem_univ y) (by linarith [ha.2] : (0:ℝ) ≤ 1 - a)
      ha.1.le (by ring)
    simp only [smul_eq_mul] at hc
    rw [le_div_iff₀ ha.1]
    nlinarith
  have := ge_of_tendsto hlim hbound
  linarith

lemma critical_is_min {f : Vec n → ℝ} (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) {x : Vec n} (hc : IsCritical f x) :
    ∀ y ∈ orthant n, f x ≤ f y := by
  intro y hy
  have h := convex_grad_ineq hf hconv x y
  have : 0 ≤ ∑ i, pd f x i * (y - x) i := by
    apply Finset.sum_nonneg
    intro i _
    simp only [PiLp.sub_apply]
    rcases (hc.1 i).lt_or_eq with h1 | h1
    · rw [hc.2.2 i h1]; simp
    · rw [← h1, sub_zero]; exact mul_nonneg (hc.2.1 i) (hy i)
  linarith


lemma vec_expand (v : Vec n) : (∑ j, v j • EuclideanSpace.single j (1:ℝ)) = v := by
  ext i
  simp [Pi.single_apply]

lemma clm_apply_expand (L : Vec n →L[ℝ] Vec n) (v : Vec n) (i : Fin n) :
    (L v) i = ∑ j, (L (EuclideanSpace.single j 1)) i * v j := by
  conv_lhs => rw [← vec_expand v]
  rw [map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl; intro j _; ring

lemma hess_apply (f : Vec n → ℝ) (p v : Vec n) (i : Fin n) :
    (fderiv ℝ (gradient f) p v) i = ∑ j, pd2 f p i j * v j := by
  rw [clm_apply_expand]
  rfl

lemma inner_hess (f : Vec n → ℝ) (p v : Vec n) :
    inner ℝ (fderiv ℝ (gradient f) p v) v = hessForm f p (fun i => v i) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, hess_apply, hessForm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma inner_grad_eq_sum (f : Vec n → ℝ) (p v : Vec n) :
    inner ℝ (gradient f p) v = ∑ i, pd f p i * v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, pd]
  apply Finset.sum_congr rfl; intro i _; ring

lemma levelset_bound {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (x0 : Vec n) {m₁ : ℝ} (hm₁ : 0 < m₁)
    (hb : ∀ y : Vec n, f y ≤ f x0 → ∀ z : Fin n → ℝ, m₁ * (z ⬝ᵥ z) ≤ hessForm f y z) :
    ∀ y, f y ≤ f x0 → ‖y - x0‖ ≤ 4 * ‖gradient f x0‖ / m₁ := by
  intro y hy
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  set v := y - x0 with hv
  have hLc : Convex ℝ {p : Vec n | f p ≤ f x0} := by
    have := hconv.convex_le (f x0)
    simpa using this
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, f (x0 + t • v) ≤ f x0 := by
    intro t ht
    have := hLc.add_smul_sub_mem (by simp only [Set.mem_setOf_eq]; exact le_rfl)
      (show y ∈ {p : Vec n | f p ≤ f x0} from hy) ht
    simpa [hv] using this
  set ψ : ℝ → ℝ := fun t => inner ℝ (gradient f (x0 + t • v)) v with hψ
  have hderiv : ∀ t : ℝ, HasDerivAt ψ (inner ℝ (fderiv ℝ (gradient f) (x0 + t • v) v) v) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x0 + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x0
    have hg := (grad_hasFDerivAt hf (x0 + t • v)).comp_hasDerivAt t hl
    have := hg.inner ℝ (hasDerivAt_const t v)
    simp only [inner_zero_right, zero_add] at this
    exact this
  have hcont : ContinuousOn ψ (Set.Icc 0 (1/2)) :=
    (continuous_iff_continuousAt.2 (fun t => (hderiv t).continuousAt)).continuousOn
  obtain ⟨τ, hτ, hτeq⟩ := exists_hasDerivAt_eq_slope ψ _ (by norm_num : (0:ℝ) < 1/2) hcont
    (fun t _ => hderiv t)
  rw [inner_hess] at hτeq
  have hvv : (fun i => v i) ⬝ᵥ (fun i => v i) = ‖v‖ ^ 2 := by
    rw [norm_sq_vec]; simp [dotProduct, sq]
  have hH := hb _ (hseg τ ⟨hτ.1.le, by linarith [hτ.2]⟩) (fun i => v i)
  rw [hvv] at hH
  have hψdiff : ψ (1/2) - ψ 0 ≥ (1/2) * (m₁ * ‖v‖ ^ 2) := by
    have : hessForm f (x0 + τ • v) (fun i => v i) = (ψ (1/2) - ψ 0) / (1/2 - 0) := hτeq
    rw [sub_zero, eq_div_iff (by norm_num)] at this
    nlinarith
  -- convexity inequalities
  set z := x0 + (1/2 : ℝ) • v with hz
  have h1 := convex_grad_ineq hdiff hconv z y
  have h2 := convex_grad_ineq hdiff hconv x0 z
  have hyz : y - z = (1/2 : ℝ) • v := by
    rw [hz, hv]; ext i; simp; ring
  have hzx : z - x0 = (1/2 : ℝ) • v := by rw [hz]; simp
  rw [hyz] at h1
  rw [hzx] at h2
  have e1 : ∑ i, pd f z i * ((1/2 : ℝ) • v) i = (1/2) * ψ (1/2) := by
    rw [hψ]; simp only [inner_grad_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; simp [hz]; ring
  have e2 : ∑ i, pd f x0 i * ((1/2 : ℝ) • v) i = (1/2) * ψ 0 := by
    rw [hψ]; simp only [inner_grad_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have hψ0 : -(‖gradient f x0‖ * ‖v‖) ≤ ψ 0 := by
    have : ψ 0 = inner ℝ (gradient f x0) v := by simp [hψ]
    rw [this]
    have := abs_real_inner_le_norm (gradient f x0) v
    linarith [neg_abs_le (inner ℝ (gradient f x0) v)]
  have hfin : m₁ * ‖v‖ ^ 2 ≤ 4 * (‖gradient f x0‖ * ‖v‖) := by nlinarith
  rcases (norm_nonneg v).lt_or_eq with hpos | hzero
  · rw [le_div_iff₀ hm₁]
    have : m₁ * ‖v‖ ≤ 4 * ‖gradient f x0‖ := by
      have := hfin
      rw [sq, ← mul_assoc] at this
      nlinarith
    linarith
  · rw [← hzero]; positivity


lemma prop4_conv {f : Vec n → ℝ}
    (hf2 : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (xs : Vec n)
    (huniq : ∀ y ∈ orthant n, (∀ z ∈ orthant n, f y ≤ f z) → y = xs)
    (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : ℕ → Vec n) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hmb : ∀ y : Vec n, f y ≤ f (x 0) → ∀ z : Fin n → ℝ,
        m₁ * (z ⬝ᵥ z) ≤ hessForm f y z ∧ hessForm f y z ≤ m₂ * (z ⬝ᵥ z))
    (hrun : IsRun f μ ε β σ (fun k => (Hmat f μ ε (x k))⁻¹) x) :
    (∀ k, x k ∈ orthant n) ∧ (∀ k, f (x k) ≤ f (x 0)) ∧
      AdmissibleScaling f μ ε (fun k => (Hmat f μ ε (x k))⁻¹) x ∧
      Tendsto x atTop (𝓝 xs) ∧ IsCritical f xs := by
  have hf1 : ContDiff ℝ 1 f := hf2.of_le (by norm_num)
  have hdiff : Differentiable ℝ f := hf1.differentiable one_ne_zero
  set D := fun k => (Hmat f μ ε (x k))⁻¹ with hD
  have hxo : ∀ k, x k ∈ orthant n := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ k =>
      obtain ⟨m, -, -, hx⟩ := hrun.2 k
      rw [hx]; exact arc_mem_orthant _ _ _ _
  have hlev : ∀ k, f (x k) ≤ f (x 0) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      obtain ⟨m, hA, -, hnext⟩ := hrun.2 k
      have props := Hinv_props hf2 μ ε hm₁ hm₂ (hmb _ ih)
      have hR := (rhs_general hpar.mu_pos hpar.eps_pos (hxo k) props.2.1 props.2.2.1
        (pow_pos hpar.beta_mem.1 m)).1
      unfold Armijo at hA
      rw [hnext]
      have := mul_nonneg hpar.sigma_mem.1.le hR
      linarith
  have hadm : AdmissibleScaling f μ ε D x := by
    intro k
    have props := Hinv_props hf2 μ ε hm₁ hm₂ (hmb _ (hlev k))
    exact ⟨props.2.1, props.2.2.1⟩
  have hB : AssumptionB f μ D x (1 / m₂) (1 / m₁) 0 0 := by
    refine ⟨by positivity, by positivity, fun k z => ?_⟩
    have props := Hinv_props hf2 μ ε hm₁ hm₂ (hmb _ (hlev k))
    simp only [pow_zero, mul_one]
    exact ⟨props.2.2.2.1 z, props.2.2.2.2 z⟩
  have hp2 := prop2_core hf1 (assumptionA_of_C2 hf2) μ ε β σ hpar D x hrun hadm _ _ 0 0 hB
  have hT : Tendsto x atTop (𝓝 xs) := by
    apply (isCompact_closedBall (x 0) (4 * ‖gradient f (x 0)‖ / m₁)).tendsto_nhds_of_unique_mapClusterPt
    · apply Eventually.of_forall
      intro k
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact levelset_bound hf2 hconv (x 0) hm₁ (fun y hy z => (hmb y hy z).1) (x k) (hlev k)
    · intro y _ hcl
      have hc := hp2 y hcl
      exact huniq y hc.1 (critical_is_min hdiff hconv hc)
  exact ⟨hxo, hlev, hadm, hT, hp2 xs hT.mapClusterPt⟩


lemma amgm_dot {m : ℝ} (hm : 0 < m) (y z : Fin n → ℝ) :
    z ⬝ᵥ y ≤ (m / 2) * (y ⬝ᵥ y) + (1 / (2 * m)) * (z ⬝ᵥ z) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have : 0 ≤ (m * y i - z i) ^ 2 / (2 * m) := by positivity
  have e : (m / 2) * (y i * y i) + (1 / (2 * m)) * (z i * z i) - z i * y i =
      (m * y i - z i) ^ 2 / (2 * m) := by field_simp; ring
  linarith

lemma mem_B (x : Vec n) (i : Fin n) : i ∈ B x ↔ x i = 0 := by simp [B]

lemma newton_step {f : Vec n → ℝ} (hf2 : ContDiff ℝ 2 f) {μ : Fin n → ℝ} {ε : ℝ}
    {xs xk : Vec n} {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hb : ∀ z : Fin n → ℝ, m₁ * (z ⬝ᵥ z) ≤ hessForm f xk z ∧ hessForm f xk z ≤ m₂ * (z ⬝ᵥ z))
    (hI : Ik f μ ε xk = B xs) (hB0 : ∀ i ∈ B xs, xk i = 0)
    (hgB : ∀ i ∈ B xs, 0 < pd f xk i) (hgJ : ∀ i ∉ B xs, pd f xs i = 0)
    (hxs : xs ∈ orthant n) :
    ‖arc f (Hmat f μ ε xk)⁻¹ xk 1 - xs‖ ≤
      (1 / m₁) * ‖gradient f xk - gradient f xs - fderiv ℝ (gradient f) xk (xk - xs)‖ := by
  set I := Ik f μ ε xk with hIdef
  set H := Hmat f μ ε xk with hH
  set D := H⁻¹ with hDdef
  obtain ⟨hpd, hDpd, hDdiag, -, -⟩ := Hinv_props hf2 μ ε hm₁ hm₂ hb
  have hHdiag : DiagonalWrt H I := by
    intro i hi j hji
    simp only [hH, Hmat]
    rw [if_pos ⟨Ne.symm hji, Or.inl hi⟩]
  set g : Fin n → ℝ := fun j => pd f xk j with hg
  set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j with hgJdef
  set e : Fin n → ℝ := fun i => xk i - xs i with he
  set r : Vec n := gradient f xk - gradient f xs - fderiv ℝ (gradient f) xk (xk - xs) with hr
  have hxsB : ∀ i ∈ I, xs i = 0 := fun i hi => (mem_B xs i).1 (hI ▸ hi)
  have heB : ∀ i ∈ I, e i = 0 := by
    intro i hi
    simp only [he, hB0 i (hI ▸ hi), hxsB i hi, sub_zero]
  set u : Fin n → ℝ := fun i => e i - (D *ᵥ gJ) i with hu
  -- Step 1
  have hstep1 : ∀ i, |(arc f D xk 1 - xs) i| ≤ |u i| := by
    intro i
    rw [PiLp.sub_apply, arc_apply, one_mul]
    by_cases hi : i ∈ I
    · have hp := dir_pos_of_mem hDpd hDdiag hi (hgB i (hI ▸ hi))
      rw [hB0 i (hI ▸ hi), hxsB i hi, zero_sub, max_eq_left (by linarith), sub_zero, abs_zero]
      exact abs_nonneg _
    · have hdir : dir f D xk i = (D *ᵥ gJ) i := mulVec_restrict hDpd.1 hDdiag g hi
      rw [hdir]
      have : xs i = max 0 (xs i) := (max_eq_right (hxs i)).symm
      rw [this]
      have := abs_max_sub_max_le_abs (xk i - (D *ᵥ gJ) i) (xs i) 0
      rw [max_comm _ 0, max_comm (xs i) 0] at this
      calc |max 0 (xk i - (D *ᵥ gJ) i) - max 0 (xs i)| ≤ |xk i - (D *ᵥ gJ) i - xs i| := this
        _ = |u i| := by congr 1; simp only [hu, he]; ring
  -- Step 2
  have hstep2 : ‖arc f D xk 1 - xs‖ ^ 2 ≤ u ⬝ᵥ u := by
    rw [norm_sq_vec]
    simp only [dotProduct]
    apply Finset.sum_le_sum
    intro i _
    rw [← sq]
    exact sq_le_sq.2 (hstep1 i)
  -- Step 3
  have hHinv : H * D = 1 := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det H).1 hpd.isUnit)
  have hHe : ∀ i, i ∉ I → (H *ᵥ e) i = (fderiv ℝ (gradient f) xk (xk - xs)) i := by
    intro i hi
    rw [hess_apply]
    simp only [mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ I
    · rw [heB j hj, PiLp.sub_apply, hB0 j (hI ▸ hj), hxsB j hj]; ring
    · have hij : ¬ (i ≠ j ∧ (i ∈ I ∨ j ∈ I)) := by tauto
      simp only [hH, Hmat, he, PiLp.sub_apply]
      rw [← hIdef, if_neg hij]
  have hHu : ∀ i, (H *ᵥ u) i = if i ∈ I then 0 else -(r i) := by
    intro i
    have hsplit : H *ᵥ u = H *ᵥ e - gJ := by
      have : u = e - D *ᵥ gJ := rfl
      rw [this, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hHinv, Matrix.one_mulVec]
    rw [hsplit, Pi.sub_apply]
    by_cases hi : i ∈ I
    · rw [if_pos hi, mulVec_diag hHdiag e hi, heB i hi]; simp [hgJdef, hi]
    · rw [if_neg hi, hHe i hi]
      have hgs := hgJ i (fun h => hi (hI ▸ h))
      simp only [hgJdef, if_neg hi, hg, hr, PiLp.sub_apply, pd] at hgs ⊢
      rw [hgs]; ring
  -- Step 4
  have hstep4 : (H *ᵥ u) ⬝ᵥ (H *ᵥ u) ≤ ‖r‖ ^ 2 := by
    rw [norm_sq_vec]
    simp only [dotProduct]
    apply Finset.sum_le_sum
    intro i _
    rw [hHu i]
    split_ifs <;> nlinarith [sq_nonneg (r i)]
  -- Step 5
  have hlow := (Hmat_bounds μ ε hb u).1
  have hag := amgm_dot hm₁ u (H *ᵥ u)
  have hdc : u ⬝ᵥ (H *ᵥ u) = (H *ᵥ u) ⬝ᵥ u := dotProduct_comm _ _
  have huu : u ⬝ᵥ u ≤ (‖r‖ / m₁) ^ 2 := by
    have h1 : (m₁ / 2) * (u ⬝ᵥ u) ≤ (1 / (2 * m₁)) * ((H *ᵥ u) ⬝ᵥ (H *ᵥ u)) := by linarith
    have h2 : (1 / (2 * m₁)) * ((H *ᵥ u) ⬝ᵥ (H *ᵥ u)) ≤ (1 / (2 * m₁)) * ‖r‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hstep4 (by positivity)
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h3 : (m₁ / 2) * (u ⬝ᵥ u) * (2 * m₁) ≤ (1 / (2 * m₁)) * ‖r‖ ^ 2 * (2 * m₁) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) (by positivity)
    have e1 : (m₁ / 2) * (u ⬝ᵥ u) * (2 * m₁) = u ⬝ᵥ u * m₁ ^ 2 := by ring
    have e2 : (1 / (2 * m₁)) * ‖r‖ ^ 2 * (2 * m₁) = ‖r‖ ^ 2 := by field_simp
    linarith
  have hfin : ‖arc f D xk 1 - xs‖ ^ 2 ≤ ((1 / m₁) * ‖r‖) ^ 2 := by
    have : (1 / m₁) * ‖r‖ = ‖r‖ / m₁ := by ring
    rw [this]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hfin


lemma remainder_bound {f : Vec n → ℝ} (hf2 : ContDiff ℝ 2 f) {xs xk : Vec n} {C : ℝ}
    (hC : ∀ y ∈ Metric.closedBall xs ‖xk - xs‖,
      ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) xk‖ ≤ C) :
    ‖gradient f xk - gradient f xs - fderiv ℝ (gradient f) xk (xk - xs)‖ ≤ C * ‖xk - xs‖ := by
  set Fk := fderiv ℝ (gradient f) xk
  set φ : Vec n → Vec n := fun y => gradient f y - Fk y with hφ
  have hdφ : ∀ y, HasFDerivAt φ (fderiv ℝ (gradient f) y - Fk) y := by
    intro y
    exact (grad_hasFDerivAt hf2 y).sub Fk.hasFDerivAt
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ)
    (s := Metric.closedBall xs ‖xk - xs‖) (x := xs) (y := xk)
    (fun y _ => (hdφ y).differentiableAt)
    (fun y hy => by rw [(hdφ y).fderiv]; exact hC y hy)
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  have : φ xk - φ xs = gradient f xk - gradient f xs - Fk (xk - xs) := by
    simp only [hφ, map_sub]; abel
  rw [← this]; exact h

lemma w_ge_coord {f : Vec n → ℝ} {μ : Fin n → ℝ} {x : Vec n} (hx : x ∈ orthant n) (i : Fin n)
    (h : x i ≤ μ i * pd f x i) : x i ≤ w f μ x := by
  unfold w
  have := PiLp.norm_apply_le (x - posPart (x - WithLp.toLp 2 (fun i => μ i * pd f x i))) i
  simp only [posPart, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs] at this
  rw [sub_max_eq_min, min_eq_left h, abs_of_nonneg (hx i)] at this
  exact this

lemma prop4_rate {n : ℕ} (f : Vec n → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (xs : Vec n) (hopt : xs ∈ orthant n ∧ ∀ y ∈ orthant n, f xs ≤ f y)
    (huniq : ∀ y ∈ orthant n, (∀ z ∈ orthant n, f y ≤ f z) → y = xs)
    (hC : AssumptionC f xs) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : ℕ → Vec n)
    (hm : ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧
      ∀ y : Vec n, f y ≤ f (x 0) → ∀ z : Fin n → ℝ,
        m₁ * (z ⬝ᵥ z) ≤ hessForm f y z ∧ hessForm f y z ≤ m₂ * (z ⬝ᵥ z))
    (hrun : IsRun f μ ε β σ (fun k => (Hmat f μ ε (x k))⁻¹) x)
    (hunit : ∀ᶠ k in atTop, Armijo f μ ε β σ ((Hmat f μ ε (x k))⁻¹) (x k) 0) :
    Tendsto x atTop (𝓝 xs) ∧
    (∀ c : ℝ, 0 < c → ∀ᶠ k in atTop,
      ‖x (k + 1) - xs‖ ≤ c * ‖x k - xs‖) ∧
    ((∃ δ : ℝ, 0 < δ ∧ ∃ L : NNReal,
      LipschitzOnWith L (fderiv ℝ (gradient f)) (Metric.ball xs δ)) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
        ‖x (k + 1) - xs‖ ≤ C * ‖x k - xs‖ ^ 2) := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hmb⟩ := hm
  obtain ⟨hxo, hlev, hadm, hT, hcrit⟩ :=
    prop4_conv hf2 hconv xs huniq μ ε β σ hpar x hm₁ hm₂ hmb hrun
  have hf1 : ContDiff ℝ 1 f := hf2.of_le (by norm_num)
  have hμ := hpar.mu_pos
  have hε := hpar.eps_pos
  have hgB := hC.2
  have hgJ : ∀ i ∉ B xs, pd f xs i = 0 := by
    intro i hi
    rw [mem_B] at hi
    exact hcrit.2.2 i (lt_of_le_of_ne (hopt.1 i) (Ne.symm hi))
  have hxs : xs ∈ orthant n := hopt.1
  -- coordinate limits
  have hxi : ∀ i, Tendsto (fun k => x k i) atTop (𝓝 (xs i)) := by
    intro i
    have : Continuous (fun y : Vec n => y i) := by fun_prop
    exact (this.tendsto xs).comp hT
  have hgi : ∀ i, Tendsto (fun k => pd f (x k) i) atTop (𝓝 (pd f xs i)) :=
    fun i => ((pd_continuous hf1 i).tendsto xs).comp hT
  have hwl : Tendsto (fun k => w f μ (x k)) atTop (𝓝 0) := by
    have := ((w_continuous hf1 μ).tendsto xs).comp hT
    rwa [w_eq_zero_of_critical hμ hcrit] at this
  -- eventual identification
  have hevB : ∀ᶠ k in atTop, ∀ i, i ∈ B xs →
      0 < pd f (x k) i ∧ x k i < ε ∧ x k i < μ i * pd f (x k) i ∧
        x k i < (1 / m₂) * pd f (x k) i := by
    rw [eventually_all]
    intro i
    by_cases hi : i ∈ B xs
    · have hx0 : xs i = 0 := (mem_B xs i).1 hi
      have hg0 := hgB i hi
      have h1 := (hgi i).eventually (lt_mem_nhds hg0)
      have h2 := (hxi i).eventually (gt_mem_nhds (show xs i < ε by rw [hx0]; exact hε))
      have h3 : ∀ᶠ k in atTop, x k i - μ i * pd f (x k) i < 0 := by
        have ht := ((hxi i).sub ((hgi i).const_mul (μ i)))
        have : xs i - μ i * pd f xs i < 0 := by rw [hx0]; nlinarith [hμ i]
        exact ht.eventually (gt_mem_nhds this)
      have h4 : ∀ᶠ k in atTop, x k i - (1 / m₂) * pd f (x k) i < 0 := by
        have ht := ((hxi i).sub ((hgi i).const_mul (1 / m₂)))
        have : xs i - (1 / m₂) * pd f xs i < 0 := by
          rw [hx0]; have : 0 < 1 / m₂ := by positivity
          nlinarith
        exact ht.eventually (gt_mem_nhds this)
      filter_upwards [h1, h2, h3, h4] with k a b c d
      exact fun _ => ⟨a, b, by linarith, by linarith⟩
    · exact Eventually.of_forall (fun k h => absurd h hi)
  have hevJ : ∀ᶠ k in atTop, ∀ i, i ∉ B xs → w f μ (x k) < x k i := by
    rw [eventually_all]
    intro i
    by_cases hi : i ∈ B xs
    · exact Eventually.of_forall (fun k h => absurd hi h)
    · have hpos : 0 < xs i := lt_of_le_of_ne (hxs i) (Ne.symm ((mem_B xs i).not.1 hi))
      have ht := (hxi i).sub hwl
      rw [sub_zero] at ht
      filter_upwards [ht.eventually (lt_mem_nhds hpos)] with k hk
      exact fun _ => by linarith
  have hIk : ∀ᶠ k in atTop, Ik f μ ε (x k) = B xs := by
    filter_upwards [hevB, hevJ] with k hB hJ
    ext i
    rw [mem_Ik]
    constructor
    · rintro ⟨h0, h1, h2⟩
      by_contra hi
      have := hJ i hi
      have : x k i ≤ w f μ (x k) := le_trans h1 (min_le_right _ _)
      linarith
    · intro hi
      obtain ⟨a, b, c, _⟩ := hB i hi
      refine ⟨hxo k i, le_min b.le (w_ge_coord (hxo k) i c.le), a⟩
  -- unit step: x (k+1) = arc 1
  have hnext : ∀ᶠ k in atTop, x (k + 1) = arc f (Hmat f μ ε (x k))⁻¹ (x k) 1 := by
    filter_upwards [hunit] with k hk
    obtain ⟨m, _, hmin, hn⟩ := hrun.2 k
    have hm0 : m = 0 := by
      by_contra hm
      exact hmin 0 (Nat.pos_of_ne_zero hm) hk
    rw [hn, hm0, pow_zero]
  -- binding coordinates vanish
  have hzero' : ∀ᶠ k in atTop, ∀ i ∈ B xs, x (k + 1) i = 0 := by
    filter_upwards [hevB, hnext] with k hB hn
    intro i hi
    obtain ⟨a, _, _, d⟩ := hB i hi
    have props := Hinv_props hf2 μ ε hm₁ hm₂ (hmb _ (hlev k))
    have hDii := diag_ge props.2.2.2.1 i
    rw [hn, arc_apply, one_mul]
    apply max_eq_left
    have hdir : dir f (Hmat f μ ε (x k))⁻¹ (x k) i =
        (Hmat f μ ε (x k))⁻¹ i i * pd f (x k) i := by
      by_cases hik : i ∈ Ik f μ ε (x k)
      · simp only [dir]; rw [mulVec_diag props.2.2.1 _ hik]
      · exfalso
        apply hik
        rw [mem_Ik]
        exact ⟨hxo k i, le_min (by linarith [hB i hi]) (w_ge_coord (hxo k) i (hB i hi).2.2.1.le),
          a⟩
    rw [hdir]
    have := mul_le_mul_of_nonneg_right hDii a.le
    linarith
  have hzero : ∀ᶠ k in atTop, ∀ i ∈ B xs, x k i = 0 := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 hzero'
    rw [eventually_atTop]
    refine ⟨K + 1, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact hK j (by omega)
  -- the Newton estimate holds eventually
  have hgood : ∀ᶠ k in atTop, ‖x (k + 1) - xs‖ ≤ (1 / m₁) *
      ‖gradient f (x k) - gradient f xs - fderiv ℝ (gradient f) (x k) (x k - xs)‖ := by
    filter_upwards [hIk, hzero, hnext, hevB] with k h1 h2 h3 h4
    rw [h3]
    exact newton_step hf2 hm₁ hm₂ (hmb _ (hlev k)) h1 h2 (fun i hi => (h4 i hi).1) hgJ hxs
  have hFc : Continuous (fderiv ℝ (gradient f)) := (grad_contDiff hf2).continuous_fderiv one_ne_zero
  have hen : ∀ δ > 0, ∀ᶠ k in atTop, ‖x k - xs‖ < δ := by
    intro δ hδ
    filter_upwards [Metric.tendsto_nhds.1 hT δ hδ] with k hk
    rwa [← dist_eq_norm]
  refine ⟨hT, ?_, ?_⟩
  · intro c hc
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuous_iff.1 hFc xs (c * m₁ / 2) (by positivity)
    filter_upwards [hgood, hen δ hδ] with k hk hd
    have hbound : ∀ y ∈ Metric.closedBall xs ‖x k - xs‖,
        ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) (x k)‖ ≤ c * m₁ := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      have h1 := hδF y (lt_of_le_of_lt hy hd)
      have h2 := hδF (x k) (by rw [dist_eq_norm]; exact hd)
      rw [dist_eq_norm] at h1 h2
      calc ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) (x k)‖
          = ‖(fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) xs) -
              (fderiv ℝ (gradient f) (x k) - fderiv ℝ (gradient f) xs)‖ := by congr 1; abel
        _ ≤ ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) xs‖ +
              ‖fderiv ℝ (gradient f) (x k) - fderiv ℝ (gradient f) xs‖ := norm_sub_le _ _
        _ ≤ c * m₁ := by linarith
    have hr := remainder_bound hf2 hbound
    calc ‖x (k + 1) - xs‖ ≤ (1 / m₁) * (c * m₁ * ‖x k - xs‖) :=
          le_trans hk (mul_le_mul_of_nonneg_left hr (by positivity))
      _ = c * ‖x k - xs‖ := by field_simp
  · rintro ⟨δ, hδ, L, hL⟩
    refine ⟨2 * L / m₁ + 1, by positivity, ?_⟩
    filter_upwards [hgood, hen δ hδ] with k hk hd
    have hL0 : (0:ℝ) ≤ L := L.2
    have hbound : ∀ y ∈ Metric.closedBall xs ‖x k - xs‖,
        ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) (x k)‖ ≤ 2 * L * ‖x k - xs‖ := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      have hyb : y ∈ Metric.ball xs δ := lt_of_le_of_lt hy hd
      have hxb : x k ∈ Metric.ball xs δ := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hd
      have := hL.dist_le_mul y hyb (x k) hxb
      rw [dist_eq_norm, dist_eq_norm] at this
      have hyx : ‖y - x k‖ ≤ 2 * ‖x k - xs‖ := by
        calc ‖y - x k‖ = ‖(y - xs) - (x k - xs)‖ := by congr 1; abel
          _ ≤ ‖y - xs‖ + ‖x k - xs‖ := norm_sub_le _ _
          _ ≤ 2 * ‖x k - xs‖ := by rw [← dist_eq_norm]; linarith
      calc _ ≤ L * ‖y - x k‖ := this
        _ ≤ L * (2 * ‖x k - xs‖) := mul_le_mul_of_nonneg_left hyx hL0
        _ = 2 * L * ‖x k - xs‖ := by ring
    have hr := remainder_bound hf2 hbound
    have he0 : 0 ≤ ‖x k - xs‖ ^ 2 := sq_nonneg _
    calc ‖x (k + 1) - xs‖ ≤ (1 / m₁) * (2 * L * ‖x k - xs‖ * ‖x k - xs‖) :=
          le_trans hk (mul_le_mul_of_nonneg_left hr (by positivity))
      _ = (2 * L / m₁) * ‖x k - xs‖ ^ 2 := by field_simp
      _ ≤ (2 * L / m₁ + 1) * ‖x k - xs‖ ^ 2 := by nlinarith


lemma armijo_of_small' {f : Vec n → ℝ} (hf : Differentiable ℝ f) {μ : Fin n → ℝ} {ε σ : ℝ}
    (hμ : ∀ i, 0 < μ i) (hε : 0 < ε)
    (hσ : σ ≤ 1) {x xbar : Vec n} (hx : x ∈ orthant n) (hxb : ‖x - xbar‖ ≤ 1)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Ik f μ ε x))
    {c2 : ℝ} (hc2 : 0 < c2) (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c2 * (u ⬝ᵥ u))
    {G : ℝ} (hG : ‖gradient f x‖ ≤ G)
    {L : NNReal} (hL : LipschitzOnWith L (gradient f) (Metric.closedBall xbar (1 + c2 * G)))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hclip : ∀ i, i ∉ Ik f μ ε x → 0 < pd f x i → a * (c2 * G) ≤ x i)
    (haL : a * (L * c2) ≤ 1 - σ) :
    σ * armijoRHS f μ ε D x a ≤ f x - f (arc f D x a) := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  set p : Fin n → ℝ := dir f D x with hp
  have hpg : p = D *ᵥ g := rfl
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  have hnn := posdef_nonneg hD
  have hgg : g ⬝ᵥ g ≤ G ^ 2 := by
    rw [hg, grad_dot]; exact pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hpp : p ⬝ᵥ p ≤ (c2 * G) ^ 2 := by
    rw [hpg]
    have h1 := cs_form hD.1 hnn hc2 hup g
    have h2 := hup g
    have h3 : c2 * (g ⬝ᵥ (D *ᵥ g)) ≤ c2 * (c2 * (g ⬝ᵥ g)) := mul_le_mul_of_nonneg_left h2 hc2.le
    have h4 : c2 * (c2 * (g ⬝ᵥ g)) ≤ c2 * (c2 * G ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgg hc2.le) hc2.le
    nlinarith
  have hpi : ∀ i, |p i| ≤ c2 * G := by
    intro i
    have : p i ^ 2 ≤ p ⬝ᵥ p := by
      have := Finset.single_le_sum (f := fun j => p j * p j) (fun j _ => mul_self_nonneg (p j))
        (Finset.mem_univ i)
      simpa [dotProduct, sq] using this
    have hK : 0 ≤ c2 * G := mul_nonneg hc2.le hG0
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  set e : Fin n → ℝ := fun i => x i - arc f D x a i with he
  have he_min : ∀ i, e i = min (x i) (a * p i) := by
    intro i; simp only [he]; rw [arc_apply, sub_max_eq_min]
  have he_sq : ∀ i, e i ^ 2 ≤ a ^ 2 * p i ^ 2 := by
    intro i
    rw [he_min]
    have hxi := hx i
    rcases le_total (x i) (a * p i) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  -- Key 1
  have hlin : armijoRHS f μ ε D x a ≤ ∑ i, g i * e i := by
    unfold armijoRHS
    rw [← hI, ← Finset.sum_compl_add_sum I (fun i => g i * e i)]
    apply add_le_add _ le_rfl
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_compl] at hi
    show a * (g i * p i) ≤ g i * e i
    rw [he_min]
    rcases le_total (a * p i) (x i) with h | h
    · rw [min_eq_right h]; ring_nf; exact le_rfl
    · rw [min_eq_left h]
      rcases le_or_gt (g i) 0 with hgi | hgi
      · nlinarith
      · have hcl := hclip i hi hgi
        have := hpi i
        have : a * p i ≤ a * (c2 * G) := by
          have := le_abs_self (p i)
          nlinarith
        have hx : x i = a * p i := le_antisymm h (by linarith)
        rw [hx]
        linarith [show a * (g i * p i) = g i * (a * p i) by ring]
  -- Key 2
  have hsq : ∑ i, e i ^ 2 ≤ a * c2 * armijoRHS f μ ε D x a := by
    unfold armijoRHS
    rw [← hI, ← Finset.sum_compl_add_sum I (fun i => e i ^ 2)]
    set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j
    have hS : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = gJ ⬝ᵥ (D *ᵥ gJ) := by
      have := quad_eq hD.1 hdiag g
      simp only [star_trivial] at this
      exact this
    have hA : ∑ i ∈ Iᶜ, e i ^ 2 ≤ a ^ 2 * (c2 * (gJ ⬝ᵥ (D *ᵥ gJ))) := by
      calc ∑ i ∈ Iᶜ, e i ^ 2 ≤ ∑ i ∈ Iᶜ, a ^ 2 * p i ^ 2 := Finset.sum_le_sum (fun i _ => he_sq i)
        _ = a ^ 2 * ∑ i ∈ Iᶜ, (D *ᵥ gJ) i ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_compl] at hi
            rw [hpg, mulVec_restrict hD.1 hdiag g hi]
        _ ≤ a ^ 2 * ((D *ᵥ gJ) ⬝ᵥ (D *ᵥ gJ)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
            have : (D *ᵥ gJ) ⬝ᵥ (D *ᵥ gJ) = ∑ i, (D *ᵥ gJ) i ^ 2 := by
              simp [dotProduct, sq]
            rw [this]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => sq_nonneg _)
        _ ≤ a ^ 2 * (c2 * (gJ ⬝ᵥ (D *ᵥ gJ))) :=
            mul_le_mul_of_nonneg_left (cs_form hD.1 hnn hc2 hup gJ) (sq_nonneg a)
    have hB : ∑ i ∈ I, e i ^ 2 ≤ a * c2 * ∑ i ∈ I, pd f x i * (x i - arc f D x a i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hgi := ((mem_Ik f μ ε x i).1 hi).2.2
      have hpi' : p i = D i i * g i := by rw [hpg, mulVec_diag hdiag g hi]
      have hDii := diag_le hup i
      have hDpos : 0 < D i i := hD.diag_pos
      show e i ^ 2 ≤ a * c2 * (g i * e i)
      have he0 : 0 ≤ e i := by
        rw [he_min]; exact le_min (hx i) (by rw [hpi']; positivity)
      have hle : e i ≤ a * p i := by rw [he_min]; exact min_le_right _ _
      have h1 : e i ^ 2 ≤ e i * (a * p i) := by nlinarith
      rw [hpi'] at h1
      have h2 : e i * (a * (D i i * g i)) ≤ e i * (a * (c2 * g i)) := by
        apply mul_le_mul_of_nonneg_left _ he0
        apply mul_le_mul_of_nonneg_left _ ha.le
        exact mul_le_mul_of_nonneg_right hDii hgi.le
      nlinarith
    rw [hS]
    nlinarith
  -- Key 3: membership in the ball
  have hnorm : ‖arc f D x a - x‖ ^ 2 = ∑ i, e i ^ 2 := by
    rw [norm_sq_vec]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, PiLp.sub_apply]
    ring
  have hsmall : ‖arc f D x a - x‖ ≤ c2 * G := by
    have h1 : ∑ i, e i ^ 2 ≤ (c2 * G) ^ 2 := by
      calc ∑ i, e i ^ 2 ≤ ∑ i, a ^ 2 * p i ^ 2 := Finset.sum_le_sum (fun i _ => he_sq i)
        _ = a ^ 2 * (p ⬝ᵥ p) := by rw [dotProduct, Finset.mul_sum]; simp [sq]
        _ ≤ 1 * (p ⬝ᵥ p) := by
            have hpp0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg (fun j _ => mul_self_nonneg (p j))
            apply mul_le_mul_of_nonneg_right _ hpp0
            nlinarith
        _ ≤ (c2 * G) ^ 2 := by linarith
    rw [← hnorm] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc2.le hG0) two_ne_zero).1 h1
  have hxmem : x ∈ Metric.closedBall xbar (1 + c2 * G) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    nlinarith [mul_nonneg hc2.le hG0]
  have harcmem : arc f D x a ∈ Metric.closedBall xbar (1 + c2 * G) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖arc f D x a - xbar‖ = ‖(arc f D x a - x) + (x - xbar)‖ := by congr 1; abel
      _ ≤ ‖arc f D x a - x‖ + ‖x - xbar‖ := norm_add_le _ _
      _ ≤ 1 + c2 * G := by linarith
  -- Key 4: descent
  have hdes := descent hf (convex_closedBall xbar (1 + c2 * G)) hL hxmem harcmem
  have hlin2 : ∑ i, pd f x i * (arc f D x a - x) i = -∑ i, g i * e i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, hg, PiLp.sub_apply]
    ring
  rw [hlin2, hnorm] at hdes
  have hRHS0 := (rhs_general hμ hε hx hD hdiag ha).1
  have hL0 : (0:ℝ) ≤ L := L.2
  have h5 : (L:ℝ) * ∑ i, e i ^ 2 ≤ L * (a * c2 * armijoRHS f μ ε D x a) :=
    mul_le_mul_of_nonneg_left hsq hL0
  have h6 : σ * armijoRHS f μ ε D x a ≤ (1 - a * (L * c2)) * armijoRHS f μ ε D x a :=
    mul_le_mul_of_nonneg_right (by linarith) hRHS0
  nlinarith


lemma exists_pos_le_fin (c : Fin n → ℝ) (S : Finset (Fin n)) (h : ∀ i ∈ S, 0 < c i) :
    ∃ ξ > 0, ∀ i ∈ S, ξ ≤ c i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨ξ, hξ, hle⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨min ξ (c a), lt_min hξ (h a (Finset.mem_insert_self a S)), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hle i hi)

lemma taylor2 {f : Vec n → ℝ} (hf2 : ContDiff ℝ 2 f) (x s : Vec n) {η : ℝ}
    (hη : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖fderiv ℝ (gradient f) (x - t • s) - fderiv ℝ (gradient f) x‖ ≤ η) :
    f (x - s) ≤ f x - inner ℝ (gradient f x) s +
      (1/2) * (inner ℝ (fderiv ℝ (gradient f) x s) s + η * ‖s‖ ^ 2) := by
  set F := fderiv ℝ (gradient f) with hF
  have hdiff : Differentiable ℝ f := hf2.differentiable (by norm_num)
  set M := inner ℝ (F x s) s + η * ‖s‖ ^ 2 with hM
  set φ1 : ℝ → ℝ := fun t => -inner ℝ (gradient f (x - t • s)) s with hφ1def
  have hl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x - t • s) (-s) t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const s).const_sub x
  have hφ : ∀ t, HasDerivAt (fun t => f (x - t • s)) (φ1 t) t := by
    intro t
    have := (hdiff (x - t • s)).hasFDerivAt.comp_hasDerivAt t (hl t)
    have e : fderiv ℝ f (x - t • s) (-s) = φ1 t := by
      rw [map_neg, hφ1def]
      simp [gradient]
    rw [e] at this
    exact this
  have hφ1 : ∀ t, HasDerivAt φ1 (inner ℝ (F (x - t • s) s) s) t := by
    intro t
    have hg := (grad_hasFDerivAt hf2 (x - t • s)).comp_hasDerivAt t (hl t)
    have := (hg.inner ℝ (hasDerivAt_const t s)).neg
    simp only [inner_zero_right, zero_add, map_neg, inner_neg_left, neg_neg] at this
    exact this
  have hφ2 : ∀ t ∈ Set.Icc (0:ℝ) 1, inner ℝ (F (x - t • s) s) s ≤ M := by
    intro t ht
    have e : inner ℝ (F (x - t • s) s) s - inner ℝ (F x s) s =
        inner ℝ ((F (x - t • s) - F x) s) s := by
      rw [_root_.sub_apply, inner_sub_left]
    have h2 : inner ℝ ((F (x - t • s) - F x) s) s ≤ η * ‖s‖ ^ 2 := by
      calc inner ℝ ((F (x - t • s) - F x) s) s ≤ ‖(F (x - t • s) - F x) s‖ * ‖s‖ :=
            real_inner_le_norm _ _
        _ ≤ ‖F (x - t • s) - F x‖ * ‖s‖ * ‖s‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ η * ‖s‖ ^ 2 := by
            have := hη t ht
            have h0 := norm_nonneg s
            nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg h0 h0)]
    linarith
  have hρ' : ∀ t ∈ Set.Icc (0:ℝ) 1, φ1 t - φ1 0 - M * t ≤ 0 := by
    intro t ht
    rcases ht.1.lt_or_eq with htp | h0
    · obtain ⟨τ, hτ, heq⟩ := exists_hasDerivAt_eq_slope φ1 _ htp
        (continuous_iff_continuousAt.2 (fun u => (hφ1 u).continuousAt)).continuousOn
        (fun u _ => hφ1 u)
      have := hφ2 τ ⟨hτ.1.le, le_trans hτ.2.le ht.2⟩
      rw [heq, sub_zero, div_le_iff₀ htp] at this
      linarith
    · rw [← h0]; simp
  set ρ : ℝ → ℝ := fun t => f (x - t • s) - φ1 0 * t - M * t ^ 2 / 2 with hρ
  have hρd : ∀ t, HasDerivAt ρ (φ1 t - φ1 0 - M * t) t := by
    intro t
    have h1 := (hφ t).sub ((hasDerivAt_id t).const_mul (φ1 0))
    have h2 := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
    have := h1.sub h2
    exact this.congr_deriv (by norm_num <;> ring)
  obtain ⟨τ, hτ, heq⟩ := exists_hasDerivAt_eq_slope ρ _ zero_lt_one
    (continuous_iff_continuousAt.2 (fun u => (hρd u).continuousAt)).continuousOn
    (fun u _ => hρd u)
  have := hρ' τ ⟨hτ.1.le, hτ.2.le⟩
  rw [heq] at this
  simp only [hρ, one_smul, zero_smul, sub_zero, mul_one, one_pow, mul_zero, zero_pow two_ne_zero,
    zero_div, div_one] at this
  have hφ0 : φ1 0 = -inner ℝ (gradient f x) s := by simp [hφ1def]
  rw [hφ0] at this
  linarith


lemma unit_local {f : Vec n → ℝ} (hf2 : ContDiff ℝ 2 f) {μ : Fin n → ℝ} {ε β σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) {xs xk : Vec n} {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hb : ∀ z : Fin n → ℝ, m₁ * (z ⬝ᵥ z) ≤ hessForm f xk z ∧ hessForm f xk z ≤ m₂ * (z ⬝ᵥ z))
    (hI : Ik f μ ε xk = B xs) (hz0 : ∀ i ∈ B xs, xk i = 0)
    {ξ : ℝ} (hX : ∀ i, i ∉ B xs → ξ ≤ xk i) (hgB : ∀ i ∈ B xs, 0 < pd f xk i)
    {ρ δ : ℝ} (hρp : 0 < ρ) (hρξ : ρ ≤ ξ) (hρδ : ρ ≤ δ / 2)
    (hΦk : (fun y => ∑ i ∈ Finset.univ.filter (fun i => i ∉ B xs), pd f y i ^ 2) xk < (m₁ * ρ) ^ 2)
    (hd : ‖xk - xs‖ < δ / 2)
    (hδF : ∀ y, dist y xs < δ →
      dist (fderiv ℝ (gradient f) y) (fderiv ℝ (gradient f) xs) < (1 - 2 * σ) * m₁ / 2) :
    Armijo f μ ε β σ ((Hmat f μ ε xk)⁻¹) xk 0 := by
  set S := Finset.univ.filter (fun i => i ∉ B xs) with hS
  set Φ : Vec n → ℝ := fun y => ∑ i ∈ S, pd f y i ^ 2 with hΦ
  set I := Ik f μ ε (xk) with hIdef
  set H := Hmat f μ ε (xk) with hH
  set D := H⁻¹ with hD
  obtain ⟨hpd, hDpd, hDdiag, hDlo, hDup⟩ := Hinv_props hf2 μ ε hm₁ hm₂ hb
  set g : Fin n → ℝ := fun j => pd f (xk) j with hg
  set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j with hgJdef
  set z := D *ᵥ gJ with hz
  have hzI : ∀ i ∈ I, z i = 0 := by
    intro i hi
    rw [hz, mulVec_diag hDdiag gJ hi]
    simp [hgJdef, hi]
  have hxI : ∀ i ∈ I, xk i = 0 := fun i hi => hz0 i (hI ▸ hi)
  have hzz : z ⬝ᵥ z ≤ (1 / m₁) * (1 / m₁) * (gJ ⬝ᵥ gJ) := by
    have h1 := cs_form hDpd.1 (posdef_nonneg hDpd) (by positivity : (0:ℝ) < 1 / m₁) hDup gJ
    have h2 := hDup gJ
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 1 / m₁)
    nlinarith
  have hgg : gJ ⬝ᵥ gJ = Φ (xk) := by
    simp only [dotProduct, hΦ, hS, Finset.sum_filter, hgJdef, hg]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hI]
    split_ifs <;> ring
  have hzz' : z ⬝ᵥ z < ρ ^ 2 := by
    have : (1 / m₁) * (1 / m₁) * (gJ ⬝ᵥ gJ) < ρ ^ 2 := by
      rw [hgg]
      have e : (1 / m₁) * (1 / m₁) * Φ (xk) = Φ (xk) / m₁ ^ 2 := by field_simp
      rw [e, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hzi : ∀ i, |z i| < ρ := by
    intro i
    have : z i ^ 2 ≤ z ⬝ᵥ z := by
      have := Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg (z j))
        (Finset.mem_univ i)
      simpa [dotProduct, sq] using this
    exact abs_lt_of_sq_lt_sq (by linarith) hρp.le
  set s : Vec n := WithLp.toLp 2 z with hsdef
  have hss : ‖s‖ ^ 2 = z ⬝ᵥ z := by
    rw [norm_sq_vec]; simp [hsdef, dotProduct, sq]
  have hsn : ‖s‖ < δ / 2 := by
    have h1 : ‖s‖ ^ 2 < (δ / 2) ^ 2 := by
      rw [hss]
      have : ρ ^ 2 ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ hρp.le hρδ 2
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) h1
  -- the unit step arc
  have harc : arc f D (xk) 1 = xk - s := by
    ext i
    rw [arc_apply, one_mul, PiLp.sub_apply]
    simp only [hsdef, PiLp.toLp_apply]
    by_cases hi : i ∈ I
    · have hp := dir_pos_of_mem hDpd hDdiag hi (hgB i (hI ▸ hi))
      rw [hxI i hi, hzI i hi, zero_sub, max_eq_left (by linarith)]; ring
    · have hdir : dir f D (xk) i = z i := mulVec_restrict hDpd.1 hDdiag g hi
      rw [hdir]
      apply max_eq_right
      have := hX i (fun h => hi (hI ▸ h))
      have := hzi i
      have := le_abs_self (z i)
      have : ρ ≤ ξ := hρξ
      linarith
  have hRHS : armijoRHS f μ ε D (xk) 1 = gJ ⬝ᵥ z := by
    unfold armijoRHS
    rw [← hIdef, harc, one_mul]
    have hS1 : ∑ i ∈ Iᶜ, pd f (xk) i * dir f D (xk) i = gJ ⬝ᵥ (D *ᵥ gJ) := by
      have := quad_eq hDpd.1 hDdiag g
      simp only [star_trivial] at this
      exact this
    rw [hS1]
    have : ∑ i ∈ I, pd f (xk) i * (xk i - (xk - s) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [PiLp.sub_apply, hsdef, PiLp.toLp_apply, hzI i hi]; ring
    rw [this, add_zero]
  have hinner_g : inner ℝ (gradient f (xk)) s = gJ ⬝ᵥ z := by
    rw [inner_grad_eq_sum]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hsdef, PiLp.toLp_apply, hgJdef, hg]
    by_cases hi : i ∈ I
    · rw [hzI i hi, if_pos hi]; ring
    · rw [if_neg hi]
  have hHz : H *ᵥ z = gJ := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H
      ((Matrix.isUnit_iff_isUnit_det H).1 hpd.isUnit), Matrix.one_mulVec]
  have hhess : hessForm f (xk) z = gJ ⬝ᵥ z := by
    rw [hessForm_eq]
    have h1 := Hmat_form f μ ε (xk) z
    have hzJ : (fun j => if j ∈ Ik f μ ε (xk) then 0 else z j) = z := by
      funext j; split_ifs with hj
      · exact (hzI j hj).symm
      · rfl
    rw [hzJ, Finset.sum_eq_zero (fun i hi => by rw [hzI i hi]; ring), zero_add] at h1
    rw [← h1, ← hH, hHz, dotProduct_comm]
  have hQ : inner ℝ (fderiv ℝ (gradient f) (xk) s) s = gJ ⬝ᵥ z := by
    rw [inner_hess]
    have : (fun i => s i) = z := by funext i; simp [hsdef]
    rw [this, hhess]
  have hQlow : m₁ * (z ⬝ᵥ z) ≤ gJ ⬝ᵥ z := by
    have := (hb z).1
    rwa [hhess] at this
  have hη : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖fderiv ℝ (gradient f) (xk - t • s) -
      fderiv ℝ (gradient f) (xk)‖ ≤ (1 - 2 * σ) * m₁ := by
    intro t ht
    have hp1 : dist (xk - t • s) xs < δ := by
      rw [dist_eq_norm]
      calc ‖xk - t • s - xs‖ = ‖(xk - xs) - t • s‖ := by congr 1; abel
        _ ≤ ‖xk - xs‖ + ‖t • s‖ := norm_sub_le _ _
        _ ≤ ‖xk - xs‖ + ‖s‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
            nlinarith [norm_nonneg s, ht.2]
        _ < δ := by linarith
    have hp2 : dist (xk) xs < δ := by rw [dist_eq_norm]; linarith
    have h1 := hδF _ hp1
    have h2 := hδF _ hp2
    rw [dist_eq_norm] at h1 h2
    calc ‖fderiv ℝ (gradient f) (xk - t • s) - fderiv ℝ (gradient f) (xk)‖
        = ‖(fderiv ℝ (gradient f) (xk - t • s) - fderiv ℝ (gradient f) xs) -
            (fderiv ℝ (gradient f) (xk) - fderiv ℝ (gradient f) xs)‖ := by congr 1; abel
      _ ≤ ‖fderiv ℝ (gradient f) (xk - t • s) - fderiv ℝ (gradient f) xs‖ +
            ‖fderiv ℝ (gradient f) (xk) - fderiv ℝ (gradient f) xs‖ := norm_sub_le _ _
      _ ≤ (1 - 2 * σ) * m₁ := by linarith
  have htay := taylor2 hf2 (xk) s hη
  rw [hinner_g, hQ, hss] at htay
  unfold Armijo
  rw [pow_zero, hRHS, harc]
  have h7 : (1 - 2 * σ) * m₁ * (z ⬝ᵥ z) ≤ (1 - 2 * σ) * (gJ ⬝ᵥ z) := by
    have := mul_le_mul_of_nonneg_left hQlow (by linarith : (0:ℝ) ≤ 1 - 2 * σ)
    linarith
  have h8 : (1 - 2 * σ) * (gJ ⬝ᵥ z) = gJ ⬝ᵥ z - 2 * (σ * (gJ ⬝ᵥ z)) := by ring
  linarith


lemma unit_step_core {n : ℕ} (f : Vec n → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (xs : Vec n) (hopt : xs ∈ orthant n ∧ ∀ y ∈ orthant n, f xs ≤ f y)
    (huniq : ∀ y ∈ orthant n, (∀ z ∈ orthant n, f y ≤ f z) → y = xs)
    (hC : AssumptionC f xs) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : ℕ → Vec n)
    (hm : ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧
      ∀ y : Vec n, f y ≤ f (x 0) → ∀ z : Fin n → ℝ,
        m₁ * (z ⬝ᵥ z) ≤ hessForm f y z ∧ hessForm f y z ≤ m₂ * (z ⬝ᵥ z))
    (hrun : IsRun f μ ε β σ (fun k => (Hmat f μ ε (x k))⁻¹) x) :
    ∀ᶠ k in atTop, Armijo f μ ε β σ ((Hmat f μ ε (x k))⁻¹) (x k) 0 := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hmb⟩ := hm
  obtain ⟨hxo, hlev, hadm, hT, hcrit⟩ :=
    prop4_conv hf2 hconv xs huniq μ ε β σ hpar x hm₁ hm₂ hmb hrun
  have hf1 : ContDiff ℝ 1 f := hf2.of_le (by norm_num)
  have hdiff : Differentiable ℝ f := hf1.differentiable one_ne_zero
  have hμ := hpar.mu_pos
  have hε := hpar.eps_pos
  have hσ0 : 0 < σ := hpar.sigma_mem.1
  have hσ1 : σ < 1 / 2 := hpar.sigma_mem.2
  have hβ0 : 0 < β := hpar.beta_mem.1
  have hβ1 : β < 1 := hpar.beta_mem.2
  have hgB := hC.2
  have hxs : xs ∈ orthant n := hopt.1
  have hgJ : ∀ i ∉ B xs, pd f xs i = 0 := by
    intro i hi
    rw [mem_B] at hi
    exact hcrit.2.2 i (lt_of_le_of_ne (hopt.1 i) (Ne.symm hi))
  have hxi : ∀ i, Tendsto (fun k => x k i) atTop (𝓝 (xs i)) := by
    intro i
    have : Continuous (fun y : Vec n => y i) := by fun_prop
    exact (this.tendsto xs).comp hT
  have hgi : ∀ i, Tendsto (fun k => pd f (x k) i) atTop (𝓝 (pd f xs i)) :=
    fun i => ((pd_continuous hf1 i).tendsto xs).comp hT
  have hwl : Tendsto (fun k => w f μ (x k)) atTop (𝓝 0) := by
    have := ((w_continuous hf1 μ).tendsto xs).comp hT
    rwa [w_eq_zero_of_critical hμ hcrit] at this
  have hevB0 : ∀ᶠ k in atTop, ∀ i, i ∈ B xs →
      0 < pd f (x k) i ∧ x k i < ε ∧ x k i < μ i * pd f (x k) i := by
    rw [eventually_all]
    intro i
    by_cases hi : i ∈ B xs
    · have hx0 : xs i = 0 := (mem_B xs i).1 hi
      have hg0 := hgB i hi
      have h1 := (hgi i).eventually (lt_mem_nhds hg0)
      have h2 := (hxi i).eventually (gt_mem_nhds (show xs i < ε by rw [hx0]; exact hε))
      have h3 : ∀ᶠ k in atTop, x k i - μ i * pd f (x k) i < 0 := by
        have ht := ((hxi i).sub ((hgi i).const_mul (μ i)))
        have : xs i - μ i * pd f xs i < 0 := by rw [hx0]; nlinarith [hμ i]
        exact ht.eventually (gt_mem_nhds this)
      filter_upwards [h1, h2, h3] with k a b c
      exact fun _ => ⟨a, b, by linarith⟩
    · exact Eventually.of_forall (fun k h => absurd h hi)
  have hevJ : ∀ᶠ k in atTop, ∀ i, i ∉ B xs → w f μ (x k) < x k i := by
    rw [eventually_all]
    intro i
    by_cases hi : i ∈ B xs
    · exact Eventually.of_forall (fun k h => absurd hi h)
    · have hpos : 0 < xs i := lt_of_le_of_ne (hxs i) (Ne.symm ((mem_B xs i).not.1 hi))
      have ht := (hxi i).sub hwl
      rw [sub_zero] at ht
      filter_upwards [ht.eventually (lt_mem_nhds hpos)] with k hk
      exact fun _ => by linarith
  have hIk : ∀ᶠ k in atTop, Ik f μ ε (x k) = B xs := by
    filter_upwards [hevB0, hevJ] with k hB hJ
    ext i
    rw [mem_Ik]
    constructor
    · rintro ⟨h0, h1, h2⟩
      by_contra hi
      have := hJ i hi
      have : x k i ≤ w f μ (x k) := le_trans h1 (min_le_right _ _)
      linarith
    · intro hi
      obtain ⟨a, b, c⟩ := hB i hi
      refine ⟨hxo k i, le_min b.le (w_ge_coord (hxo k) i c.le), a⟩
  -- the free coordinates stay bounded away from zero
  obtain ⟨ξ, hξ, hξle⟩ := exists_pos_le_fin (fun i => xs i / 2)
    (Finset.univ.filter (fun i => i ∉ B xs)) (by
      intro i hi
      have hi' := (Finset.mem_filter.1 hi).2
      have : 0 < xs i := lt_of_le_of_ne (hxs i) (Ne.symm ((mem_B xs i).not.1 hi'))
      simp only; linarith)
  have hevX : ∀ᶠ k in atTop, ∀ i, i ∉ B xs → ξ ≤ x k i := by
    rw [eventually_all]
    intro i
    by_cases hi : i ∈ B xs
    · exact Eventually.of_forall (fun k h => absurd hi h)
    · have hpos : 0 < xs i := lt_of_le_of_ne (hxs i) (Ne.symm ((mem_B xs i).not.1 hi))
      have hle := hξle i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
      simp only at hle
      filter_upwards [(hxi i).eventually (lt_mem_nhds (by linarith : xs i / 2 < xs i))]
        with k hk
      exact fun _ => by linarith
  -- constants for the stepsize bound
  set c2 := 1 / m₁ with hc2
  have hc2p : 0 < c2 := by positivity
  set G := ‖gradient f xs‖ + 1 with hG
  have hG1 : 1 ≤ G := by rw [hG]; linarith [norm_nonneg (gradient f xs)]
  obtain ⟨L, hL⟩ := assumptionA_of_C2 hf2 (Metric.closedBall xs (1 + c2 * G))
    Metric.isBounded_closedBall
  have hL0 : (0:ℝ) ≤ L := L.2
  set abar := min 1 (min (ξ / (c2 * G)) ((1 - σ) / (L * c2 + 1))) with habar
  have hc2G : 0 < c2 * G := mul_pos hc2p (by linarith)
  have hLc : 0 < (L:ℝ) * c2 + 1 := by nlinarith
  have habarp : 0 < abar :=
    lt_min one_pos (lt_min (div_pos hξ hc2G) (div_pos (by linarith) hLc))
  have habar1 : abar ≤ 1 := min_le_left _ _
  have habarξ : abar * (c2 * G) ≤ ξ := by
    have : abar ≤ ξ / (c2 * G) := le_trans (min_le_right _ _) (min_le_left _ _)
    rwa [le_div_iff₀ hc2G] at this
  have habarL : abar * (L * c2) ≤ 1 - σ := by
    have : abar ≤ (1 - σ) / (L * c2 + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ hLc] at this
    nlinarith
  set a0 := β * abar with ha0
  have ha0p : 0 < a0 := mul_pos hβ0 habarp
  have hev1 : ∀ᶠ k in atTop, ‖x k - xs‖ ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.1 hT 1 one_pos] with k hk
    rw [← dist_eq_norm]; exact hk.le
  have hev3 : ∀ᶠ k in atTop, ‖gradient f (x k)‖ ≤ G := by
    have hglim : Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 ‖gradient f xs‖) :=
      ((continuous_norm.comp (grad_continuous hf1)).tendsto xs).comp hT
    filter_upwards [hglim.eventually (Iio_mem_nhds (by linarith : ‖gradient f xs‖ < G))]
      with k hk
    exact hk.le
  have hevB1 : ∀ᶠ k in atTop, ∀ i, i ∈ B xs → x k i < a0 * ((1 / m₂) * pd f (x k) i) := by
    rw [eventually_all]
    intro i
    by_cases hi : i ∈ B xs
    · have hx0 : xs i = 0 := (mem_B xs i).1 hi
      have hg0 := hgB i hi
      have ht := ((hxi i).sub ((hgi i).const_mul (a0 * (1 / m₂))))
      have : xs i - a0 * (1 / m₂) * pd f xs i < 0 := by
        rw [hx0]; have : 0 < a0 * (1 / m₂) := by positivity
        nlinarith
      filter_upwards [ht.eventually (gt_mem_nhds this)] with k hk
      exact fun _ => by linarith
    · exact Eventually.of_forall (fun k h => absurd h hi)
  have hzero' : ∀ᶠ k in atTop, ∀ i ∈ B xs, x (k + 1) i = 0 := by
    filter_upwards [hIk, hevB0, hevX, hev1, hev3, hevB1] with k hI hB hX h1 h3 hB1
    have props := Hinv_props hf2 μ ε hm₁ hm₂ (hmb _ (hlev k))
    obtain ⟨m, hAm, hmin, hn⟩ := hrun.2 k
    have harm : ∀ m' : ℕ, β ^ m' ≤ abar →
        Armijo f μ ε β σ ((Hmat f μ ε (x k))⁻¹) (x k) m' := by
      intro m' hm'
      unfold Armijo
      have hpos : 0 < β ^ m' := pow_pos hβ0 m'
      refine armijo_of_small' hdiff hμ hε (by linarith) (hxo k) h1 props.2.1 props.2.2.1 hc2p
        props.2.2.2.2 h3 hL hpos (le_trans hm' habar1) ?_
        (le_trans (mul_le_mul_of_nonneg_right hm' (by positivity)) habarL)
      intro i hi _
      rw [hI] at hi
      have := hX i hi
      have : β ^ m' * (c2 * G) ≤ abar * (c2 * G) := mul_le_mul_of_nonneg_right hm' hc2G.le
      linarith
    have hm_ge : a0 ≤ β ^ m := by
      by_contra hlt
      push Not at hlt
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hlt
        have : β * abar < 1 := by nlinarith
        linarith
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have : β ^ m' ≤ abar := by
        rw [pow_succ] at hlt
        have := (mul_lt_mul_iff_of_pos_right hβ0).1 (by linarith : β ^ m' * β < abar * β)
        exact this.le
      exact hmin m' (Nat.lt_succ_self m') (harm m' this)
    intro i hi
    have hiI : i ∈ Ik f μ ε (x k) := hI ▸ hi
    have hDii := diag_ge props.2.2.2.1 i
    obtain ⟨a, _, _⟩ := hB i hi
    have hdir : dir f (Hmat f μ ε (x k))⁻¹ (x k) i =
        (Hmat f μ ε (x k))⁻¹ i i * pd f (x k) i := by
      simp only [dir]; rw [mulVec_diag props.2.2.1 _ hiI]
    rw [hn, arc_apply, hdir]
    apply max_eq_left
    have h5 := hB1 i hi
    have h6 : a0 * ((1 / m₂) * pd f (x k) i) ≤
        β ^ m * ((Hmat f μ ε (x k))⁻¹ i i * pd f (x k) i) := by
      apply mul_le_mul hm_ge _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hDii a.le
    linarith
  have hzero : ∀ᶠ k in atTop, ∀ i ∈ B xs, x k i = 0 := by
    obtain ⟨K, hK⟩ := eventually_atTop.1 hzero'
    rw [eventually_atTop]
    refine ⟨K + 1, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact hK j (by omega)
  -- the reduced gradient tends to zero
  set S := Finset.univ.filter (fun i => i ∉ B xs) with hS
  set Φ : Vec n → ℝ := fun y => ∑ i ∈ S, pd f y i ^ 2 with hΦ
  have hΦc : Continuous Φ := by
    apply continuous_finsetSum
    intro i _
    exact (pd_continuous hf1 i).pow 2
  have hΦ0 : Φ xs = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hgJ i (Finset.mem_filter.1 hi).2]; ring
  have hFc : Continuous (fderiv ℝ (gradient f)) :=
    (grad_contDiff hf2).continuous_fderiv one_ne_zero
  have hη0 : 0 < (1 - 2 * σ) * m₁ := by nlinarith
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuous_iff.1 hFc xs ((1 - 2 * σ) * m₁ / 2) (by linarith)
  set ρ := min ξ (δ / 2) with hρ
  have hρp : 0 < ρ := lt_min hξ (by linarith)
  have hevΦ : ∀ᶠ k in atTop, Φ (x k) < (m₁ * ρ) ^ 2 := by
    have := ((hΦc.tendsto xs).comp hT)
    rw [hΦ0] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  have hen : ∀ᶠ k in atTop, ‖x k - xs‖ < δ / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hT (δ / 2) (by linarith)] with k hk
    rwa [← dist_eq_norm]
  filter_upwards [hIk, hzero, hevX, hevB0, hevΦ, hen] with k hI hz0 hX hB hΦk hd
  exact unit_local hf2 hσ0 hσ1 hm₁ hm₂ (hmb _ (hlev k)) hI hz0 hX (fun i hi => (hB i hi).1)
    hρp (min_le_left _ _) (min_le_right _ _) hΦk hd hδF

end ProjNewton.Superlinear

open ProjNewton.Superlinear Matrix Filter Topology

theorem solution {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (xs : Vec n) (hopt : xs ∈ orthant n ∧ ∀ y ∈ orthant n, f xs ≤ f y)
    (huniq : ∀ y ∈ orthant n, (∀ z ∈ orthant n, f y ≤ f z) → y = xs)
    (hC : AssumptionC f xs) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : ℕ → Vec n)
    (hm : ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧
      ∀ y : Vec n, f y ≤ f (x 0) → ∀ z : Fin n → ℝ,
        m₁ * (z ⬝ᵥ z) ≤ hessForm f y z ∧ hessForm f y z ≤ m₂ * (z ⬝ᵥ z))
    (hrun : IsRun f μ ε β σ (fun k => (Hmat f μ ε (x k))⁻¹) x) :
    ∀ᶠ k in atTop, Armijo f μ ε β σ ((Hmat f μ ε (x k))⁻¹) (x k) 0 :=
  unit_step_core f hf2 hconv xs hopt huniq hC μ ε β σ hpar x hm hrun
