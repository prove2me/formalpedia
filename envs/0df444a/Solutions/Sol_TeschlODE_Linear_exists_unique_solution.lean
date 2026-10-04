-- Prove2me | solution 1 for TeschlODE.Linear.exists_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:21:39.099045+00:00
-- url     : https://prove2.me/submissions/02fde3e5-3cfb-4e03-96a9-30cc49a90bb5

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsSolution

open Set Filter
open scoped Matrix NNReal Topology

namespace LinSysAux

/-- Multiplication by a real matrix as a continuous linear map on `ℝⁿ`. -/
noncomputable def mvCLM {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin n → ℝ) (F' := Fin n → ℝ)).toLinearMap ∘ₗ
    (Matrix.toLin' : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).toLinearMap

lemma mvCLM_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    mvCLM B x = B *ᵥ x := by
  simp [mvCLM]

lemma continuous_mvCLM {n : ℕ} : Continuous (mvCLM (n := n)) :=
  LinearMap.continuous_of_finiteDimensional _

/-- On a compact set where `A` is continuous, the maps `x ↦ A t x` are uniformly Lipschitz. -/
lemma exists_lipschitz_bound {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {S : Set ℝ}
    (hS : IsCompact S) (hA : ContinuousOn A S) :
    ∃ K : ℝ≥0, ∀ t ∈ S, LipschitzWith K (fun x : Fin n → ℝ => A t *ᵥ x) := by
  have hc : ContinuousOn (fun s => ‖mvCLM (A s)‖) S := (continuous_mvCLM.comp_continuousOn hA).norm
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨K.toNNReal, fun t ht => ?_⟩
  have h1 : ‖mvCLM (A t)‖₊ ≤ K.toNNReal := by
    have := hK t ht
    rw [Real.norm_eq_abs, abs_norm] at this
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact this.trans (le_max_left _ _)
  have h2 := (mvCLM (A t)).lipschitz
  have h3 : (⇑(mvCLM (A t)) : (Fin n → ℝ) → (Fin n → ℝ)) = fun x => A t *ᵥ x :=
    funext (mvCLM_apply _)
  rw [h3] at h2
  exact h2.weaken h1

/-! ### Derivatives within `Icc` restrict to one-sided derivatives -/

lemma hasDerivWithinAt_Ici_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {a b t : ℝ} (ht : t ∈ Ico a b)
    (h : HasDerivWithinAt f f' (Icc a b) t) : HasDerivWithinAt f f' (Ici t) t := by
  refine h.mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

lemma hasDerivWithinAt_Iic_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {a b t : ℝ} (ht : t ∈ Ioc a b)
    (h : HasDerivWithinAt f f' (Icc a b) t) : HasDerivWithinAt f f' (Iic t) t := by
  refine h.mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)

/-! ### Clamping -/

/-- Coordinatewise clamp to `[-R, R]`. -/
def clamp {n : ℕ} (R : ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun i => max (-R) (min R (y i))

lemma clamp_lipschitz {n : ℕ} (R : ℝ) : LipschitzWith 1 (clamp (n := n) R) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  have hi : dist (y i) (z i) ≤ dist y z := dist_le_pi_dist y z i
  refine le_trans ?_ hi
  simp only [clamp, Real.dist_eq]
  have e1 := abs_min_sub_min_le_max R (y i) R (z i)
  have e2 := abs_max_sub_max_le_abs (min R (y i)) (min R (z i)) (-R)
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at e1
  rw [max_comm (-R), max_comm (-R)]
  exact e2.trans e1

lemma clamp_zero {n : ℕ} {R : ℝ} (hR : 0 ≤ R) : clamp (n := n) R 0 = 0 := by
  funext i
  simp [clamp, hR]

lemma clamp_norm_le {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (y : Fin n → ℝ) : ‖clamp R y‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  simp only [clamp]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clamp_eq_of_norm_le {n : ℕ} {R : ℝ} {y : Fin n → ℝ} (h : ‖y‖ ≤ R) : clamp R y = y := by
  funext i
  have hi : |y i| ≤ R := by
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    exact this.trans h
  rw [abs_le] at hi
  simp only [clamp]
  rw [min_eq_right hi.2, max_eq_right hi.1]

/-! ### Gronwall bound -/

lemma gronwall_right {n : ℕ} {a b : ℝ} {K : ℝ≥0} {v : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
    (hv : ∀ t ∈ Icc a b, LipschitzWith K (v t)) (hv0 : ∀ t ∈ Icc a b, v t 0 = 0)
    {α : ℝ → Fin n → ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (v t (α t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, ‖α t‖ ≤ ‖α a‖ * Real.exp (K * (t - a)) := by
  have hcont : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousWithinAt
  have key := dist_le_of_trajectories_ODE_of_mem (v := v) (s := fun _ => univ) (K := K)
    (f := α) (g := fun _ => 0) (a := a) (b := b) (δ := ‖α a‖)
    (fun t ht => (hv t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    hcont
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hα t (Ico_subset_Icc_self ht)))
    (fun _ _ => trivial)
    continuousOn_const
    (fun t ht => by
      rw [show v t ((fun _ => (0 : Fin n → ℝ)) t) = 0 from hv0 t (Ico_subset_Icc_self ht)]
      exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => trivial) (by simp)
  intro t ht
  simpa using key t ht

lemma gronwall {n : ℕ} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) {K : ℝ≥0}
    {v : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
    (hv : ∀ t ∈ Icc a b, LipschitzWith K (v t)) (hv0 : ∀ t ∈ Icc a b, v t 0 = 0)
    {α : ℝ → Fin n → ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (v t (α t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, ‖α t‖ ≤ ‖α t₀‖ * Real.exp (K * |t - t₀|) := by
  intro t ht
  rcases le_total t₀ t with h | h
  · have key := gronwall_right (a := t₀) (b := b) (K := K) (v := v)
      (fun s hs => hv s ⟨ht₀.1.trans hs.1, hs.2⟩) (fun s hs => hv0 s ⟨ht₀.1.trans hs.1, hs.2⟩)
      (α := α) (fun s hs => (hα s ⟨ht₀.1.trans hs.1, hs.2⟩).mono (Icc_subset_Icc_left ht₀.1))
      t ⟨h, ht.2⟩
    rwa [abs_of_nonneg (sub_nonneg.2 h)]
  · -- reflect time at `t₀`
    set c : ℝ := 2 * t₀ with hc
    let β : ℝ → Fin n → ℝ := fun s => α (c - s)
    let w : ℝ → (Fin n → ℝ) → (Fin n → ℝ) := fun s y => -(v (c - s) y)
    have hmem : ∀ s ∈ Icc t₀ (c - a), c - s ∈ Icc a b := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1, ht₀.2]⟩
    have hβ : ∀ s ∈ Icc t₀ (c - a), HasDerivWithinAt β (w s (β s)) (Icc t₀ (c - a)) s := by
      intro s hs
      have h1 := hα (c - s) (hmem s hs)
      have h2 : HasDerivWithinAt (fun s : ℝ => c - s) (-1) (Icc t₀ (c - a)) s :=
        ((hasDerivAt_id s).const_sub c).hasDerivWithinAt
      have hmap : MapsTo (fun s : ℝ => c - s) (Icc t₀ (c - a)) (Icc a b) := fun s hs => hmem s hs
      have h3 := h1.scomp s h2 hmap
      exact h3.congr_deriv (by simp [w, β])
    have hwL : ∀ s ∈ Icc t₀ (c - a), LipschitzWith K (w s) := by
      intro s hs
      have hL := LipschitzWith.id.neg.comp (hv _ (hmem s hs))
      rw [one_mul] at hL
      exact hL
    have hw0 : ∀ s ∈ Icc t₀ (c - a), w s 0 = 0 := by
      intro s hs
      simp [w, hv0 _ (hmem s hs)]
    have key := gronwall_right (a := t₀) (b := c - a) (K := K) (v := w) hwL hw0 (α := β) hβ
      (c - t) ⟨by linarith, by linarith [ht.1]⟩
    have e1 : β (c - t) = α t := by simp [β]
    have e2 : β t₀ = α t₀ := by simp [β, hc]; ring_nf
    rw [e1, e2] at key
    rw [abs_of_nonpos (sub_nonpos.2 h)]
    have e3 : (c - t - t₀) = -(t - t₀) := by rw [hc]; ring
    rwa [e3] at key

/-! ### Existence on a compact interval -/

lemma norm_mulVec_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K (fun x : Fin n → ℝ => B *ᵥ x)) (y : Fin n → ℝ) :
    ‖B *ᵥ y‖ ≤ K * ‖y‖ := by
  have := hK.dist_le_mul y 0
  simpa [dist_eq_norm] using this

/-- Picard–Lindelöf for the truncated field `A(t) · clamp(x)`. -/
lemma exists_trunc_solution {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b)) (x₀ : Fin n → ℝ) {R : ℝ}
    (hR : 0 ≤ R) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, LipschitzWith K (fun x : Fin n → ℝ => A t *ᵥ x)) :
    ∃ α : ℝ → Fin n → ℝ, α t₀ = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (A t *ᵥ clamp R (α t)) (Icc a b) t := by
  set v : ℝ → (Fin n → ℝ) → (Fin n → ℝ) := fun t x => A t *ᵥ clamp R x with hv
  have hvL : ∀ t ∈ Icc a b, LipschitzWith K (v t) := fun t ht => by
    have := (hK t ht).comp (clamp_lipschitz (n := n) R)
    rwa [mul_one] at this
  have hvB : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ K * R := fun t ht x =>
    (norm_mulVec_le (hK t ht) _).trans (by gcongr; exact clamp_norm_le hR x)
  have hmax : 0 ≤ max (b - t₀) (t₀ - a) := le_max_of_le_left (sub_nonneg.2 ht₀.2)
  let L : ℝ≥0 := K * R.toNNReal
  let a' : ℝ≥0 := L * (max (b - t₀) (t₀ - a)).toNNReal
  have hL : (L : ℝ) = K * R := by simp [L, Real.coe_toNNReal _ hR]
  have ha' : (a' : ℝ) = K * R * max (b - t₀) (t₀ - a) := by
    simp [a', hL, Real.coe_toNNReal _ hmax]
  have hPL : IsPicardLindelof v (tmin := a) (tmax := b) ⟨t₀, ht₀⟩ x₀ a' 0 L K :=
    { lipschitzOnWith := fun t ht => (hvL t ht).lipschitzOnWith
      continuousOn := fun x _ => by
        have h1 : ContinuousOn (fun t => mvCLM (A t) (clamp R x)) (Icc a b) :=
          ((ContinuousLinearMap.apply ℝ (Fin n → ℝ) (clamp R x)).continuous.comp
            continuous_mvCLM).comp_continuousOn hA
        exact h1.congr fun t _ => (mvCLM_apply _ _).symm
      norm_le := fun t ht x _ => by rw [hL]; exact hvB t ht x
      mul_max_le := by
        simp only [NNReal.coe_zero, sub_zero]
        rw [ha', hL] }
  obtain ⟨α, h0, hd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hd⟩

lemma exists_compact {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b)) (x₀ : Fin n → ℝ) :
    ∃ α : ℝ → Fin n → ℝ, α t₀ = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (A t *ᵥ α t) (Icc a b) t := by
  obtain ⟨K, hK⟩ := exists_lipschitz_bound (isCompact_Icc (a := a) (b := b)) hA
  set R : ℝ := ‖x₀‖ * Real.exp (K * (b - a)) + 1 with hRdef
  have hR : 0 ≤ R := by positivity
  obtain ⟨α, h0, hd⟩ := exists_trunc_solution ht₀ hA x₀ hR hK
  have hvL : ∀ t ∈ Icc a b, LipschitzWith K
      (fun x : Fin n → ℝ => A t *ᵥ clamp R x) := fun t ht => by
    have := (hK t ht).comp (clamp_lipschitz (n := n) R)
    rwa [mul_one] at this
  have hv0 : ∀ t ∈ Icc a b, (fun x : Fin n → ℝ => A t *ᵥ clamp R x) 0 = 0 := fun t _ => by
    simp [clamp_zero hR]
  have hg := gronwall ht₀ (v := fun t x => A t *ᵥ clamp R x) hvL hv0 hd
  have hball : ∀ t ∈ Icc a b, ‖α t‖ ≤ R := by
    intro t ht
    have h1 := hg t ht
    rw [h0] at h1
    have h2 : |t - t₀| ≤ b - a :=
      abs_le.2 ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
    calc ‖α t‖ ≤ ‖x₀‖ * Real.exp (K * |t - t₀|) := h1
      _ ≤ ‖x₀‖ * Real.exp (K * (b - a)) := by gcongr
      _ ≤ R := by linarith
  refine ⟨α, h0, fun t ht => ?_⟩
  have := hd t ht
  rwa [clamp_eq_of_norm_le (hball t ht)] at this

/-! ### Uniqueness -/

lemma unique_compact {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b)) {f g : ℝ → Fin n → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (A t *ᵥ f t) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (A t *ᵥ g t) (Icc a b) t)
    (h0 : f t₀ = g t₀) : EqOn f g (Icc a b) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_bound (isCompact_Icc (a := a) (b := b)) hA
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousWithinAt
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  apply EqOn.union
  · have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    refine ODE_solution_unique_of_mem_Icc_left (v := fun t x => A t *ᵥ x) (s := fun _ => univ)
      (K := K) (a := a) (b := t₀) (fun t ht => (hK t (hsub (Ioc_subset_Icc_self ht))).lipschitzOnWith)
      (hfc.mono hsub) (fun t ht => ?_) (fun _ _ => trivial) (hgc.mono hsub)
      (fun t ht => ?_) (fun _ _ => trivial) h0
    · exact ((hf t (hsub (Ioc_subset_Icc_self ht))).mono hsub |> hasDerivWithinAt_Iic_of_Icc ht)
    · exact ((hg t (hsub (Ioc_subset_Icc_self ht))).mono hsub |> hasDerivWithinAt_Iic_of_Icc ht)
  · have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t x => A t *ᵥ x) (s := fun _ => univ)
      (K := K) (a := t₀) (b := b) (fun t ht => (hK t (hsub (Ico_subset_Icc_self ht))).lipschitzOnWith)
      (hfc.mono hsub) (fun t ht => ?_) (fun _ _ => trivial) (hgc.mono hsub)
      (fun t ht => ?_) (fun _ _ => trivial) h0
    · exact ((hf t (hsub (Ico_subset_Icc_self ht))).mono hsub |> hasDerivWithinAt_Ici_of_Icc ht)
    · exact ((hg t (hsub (Ico_subset_Icc_self ht))).mono hsub |> hasDerivWithinAt_Ici_of_Icc ht)

lemma unique_on {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) {f g : ℝ → Fin n → ℝ}
    (hf : TeschlODE.Linear.IsSolution A I f) (hg : TeschlODE.Linear.IsSolution A I g)
    (h0 : f t₀ = g t₀) : EqOn f g I := by
  intro t ht
  have hsub : Icc (min t₀ t) (max t₀ t) ⊆ I := hI.uIcc_subset ht₀ ht
  have := unique_compact (a := min t₀ t) (b := max t₀ t) (t₀ := t₀)
    ⟨min_le_left _ _, le_max_left _ _⟩ (hA.mono hsub)
    (fun s hs => (hf s (hsub hs)).mono hsub) (fun s hs => (hg s (hsub hs)).mono hsub) h0
  exact this ⟨min_le_right _ _, le_max_right _ _⟩

/-! ### Existence on a general interval -/

lemma exists_on_I {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hA : ContinuousOn A I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (x₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, TeschlODE.Linear.IsSolution A I x ∧ x t₀ = x₀ := by
  classical
  have hsub : ∀ {u v : ℝ}, u ∈ I → v ∈ I → Icc (min u v) (max u v) ⊆ I :=
    fun hu hv => hI.uIcc_subset hu hv
  have hex : ∀ t ∈ I, ∃ α : ℝ → Fin n → ℝ, α t₀ = x₀ ∧
      ∀ s ∈ Icc (min t₀ t) (max t₀ t),
        HasDerivWithinAt α (A s *ᵥ α s) (Icc (min t₀ t) (max t₀ t)) s := fun t ht =>
    exists_compact ⟨min_le_left _ _, le_max_left _ _⟩ (hA.mono (hsub ht₀ ht)) x₀
  choose! sol hsol0 hsold using hex
  set x : ℝ → Fin n → ℝ := fun t => sol t t with hx
  have hminI : ∀ {u v : ℝ}, u ∈ I → v ∈ I → min u v ∈ I := fun {u v} hu hv => by
    rcases min_choice u v with h | h <;> rw [h] <;> assumption
  have hmaxI : ∀ {u v : ℝ}, u ∈ I → v ∈ I → max u v ∈ I := fun {u v} hu hv => by
    rcases max_choice u v with h | h <;> rw [h] <;> assumption
  -- `x` agrees with any solution on a compact subinterval containing `t₀`
  have K1 : ∀ {a b : ℝ}, a ∈ I → b ∈ I → t₀ ∈ Icc a b → ∀ α : ℝ → Fin n → ℝ, α t₀ = x₀ →
      (∀ s ∈ Icc a b, HasDerivWithinAt α (A s *ᵥ α s) (Icc a b) s) →
      ∀ s ∈ Icc a b, x s = α s := by
    intro a b ha hb ht α hα0 hαd s hs
    have hab : Icc a b ⊆ I := hI.out ha hb
    have hsI : s ∈ I := hab hs
    have hJ : Icc (min t₀ s) (max t₀ s) ⊆ Icc a b :=
      Icc_subset_Icc (le_min ht.1 hs.1) (max_le ht.2 hs.2)
    have := unique_compact (a := min t₀ s) (b := max t₀ s) (t₀ := t₀)
      ⟨min_le_left _ _, le_max_left _ _⟩ (hA.mono (hab.trans' hJ))
      (f := sol s) (g := α) (hsold s hsI) (fun u hu => (hαd u (hJ hu)).mono hJ)
      (by rw [hsol0 s hsI, hα0])
    exact this ⟨min_le_right _ _, le_max_right _ _⟩
  have hlocal : ∀ a b, a ∈ I → b ∈ I → t₀ ∈ Icc a b → ∀ s ∈ Icc a b,
      HasDerivWithinAt x (A s *ᵥ x s) (Icc a b) s := by
    intro a b ha hb ht s hs
    obtain ⟨α, hα0, hαd⟩ := exists_compact ht (hA.mono (hI.out ha hb)) x₀
    have hEq : EqOn x α (Icc a b) := fun u hu => K1 ha hb ht α hα0 hαd u hu
    exact ((hαd s hs).congr hEq (hEq hs)).congr_deriv (by rw [hEq hs])
  have hright : ∀ s ∈ I, HasDerivWithinAt x (A s *ᵥ x s) (I ∩ Ici s) s := by
    intro s hs
    by_cases hb : ∃ b' ∈ I, s < b'
    · obtain ⟨b', hb'I, hsb'⟩ := hb
      have h1 := hlocal (min t₀ s) (max t₀ b') (hminI ht₀ hs) (hmaxI ht₀ hb'I)
        ⟨min_le_left _ _, le_max_left _ _⟩ s
        ⟨min_le_right _ _, le_max_of_le_right hsb'.le⟩
      have h2 := h1.mono (Icc_subset_Icc (min_le_right t₀ s) (le_max_right t₀ b'))
      refine h2.mono_of_mem_nhdsWithin ?_
      exact nhdsWithin_mono _ inter_subset_right (Icc_mem_nhdsGE hsb')
    · push Not at hb
      have hsing : (I ∩ Ici s).Subsingleton := fun u hu v hv =>
        (le_antisymm (hb u hu.1) hu.2).trans (le_antisymm (hb v hv.1) hv.2).symm
      exact hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_subsingleton hsing)
  have hleft : ∀ s ∈ I, HasDerivWithinAt x (A s *ᵥ x s) (I ∩ Iic s) s := by
    intro s hs
    by_cases ha : ∃ a' ∈ I, a' < s
    · obtain ⟨a', ha'I, ha's⟩ := ha
      have h1 := hlocal (min t₀ a') (max t₀ s) (hminI ht₀ ha'I) (hmaxI ht₀ hs)
        ⟨min_le_left _ _, le_max_left _ _⟩ s
        ⟨min_le_of_right_le ha's.le, le_max_right _ _⟩
      have h2 := h1.mono (Icc_subset_Icc (min_le_right t₀ a') (le_max_right t₀ s))
      refine h2.mono_of_mem_nhdsWithin ?_
      exact nhdsWithin_mono _ inter_subset_right (Icc_mem_nhdsLE ha's)
    · push Not at ha
      have hsing : (I ∩ Iic s).Subsingleton := fun u hu v hv =>
        (le_antisymm hu.2 (ha u hu.1)).trans (le_antisymm hv.2 (ha v hv.1)).symm
      exact hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_subsingleton hsing)
  refine ⟨x, fun s hs => ?_, hsol0 t₀ ht₀⟩
  have hU : I ∩ Iic s ∪ I ∩ Ici s = I := by
    rw [← inter_union_distrib_left, Iic_union_Ici, inter_univ]
  have := (hleft s hs).union (hright s hs)
  rwa [hU] at this

end LinSysAux

theorem solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (x₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, TeschlODE.Linear.IsSolution A I x ∧ x t₀ = x₀ ∧
      ∀ y : ℝ → Fin n → ℝ, TeschlODE.Linear.IsSolution A I y → y t₀ = x₀ → Set.EqOn y x I := by
  obtain ⟨x, hx, hx0⟩ := LinSysAux.exists_on_I hI hA ht₀ x₀
  exact ⟨x, hx, hx0, fun y hy hy0 => LinSysAux.unique_on hI hA ht₀ hy hx (hy0.trans hx0.symm)⟩
