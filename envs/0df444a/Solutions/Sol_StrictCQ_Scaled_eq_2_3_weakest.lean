-- Prove2me | solution 1 for StrictCQ.Scaled.eq_2_3_weakest
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:11:55.898381+00:00
-- url     : https://prove2.me/submissions/1e43883c-6c76-4d68-bf58-2da5d004d890

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace RRAux_StrictCQ_Scaled_eq_2_3_weakest

open StrictCQ.Scaled

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma grad_cont {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  show Continuous fun x => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x)
  exact (LinearIsometryEquiv.continuous _).comp (hf.continuous_fderiv one_ne_zero)

/-- MFCQ excludes nontrivial nonnegative active dependences. -/
lemma mfcq_no_dep {n m p : ℕ} (C : Constraints n m p) (xs : E n) (hM : C.MFCQ xs)
    (L : Fin m → ℝ) (U : Fin p → ℝ) (hU0 : ∀ j, 0 ≤ U j) (hUc : ∀ j, C.g j xs ≠ 0 → U j = 0)
    (hsum : ∑ i, L i • gradient (C.h i) xs + ∑ j, U j • gradient (C.g j) xs = 0) :
    L = 0 ∧ U = 0 := by
  obtain ⟨hli, d, hd1, hd2⟩ := hM
  have hin : ∑ i, L i * ⟪gradient (C.h i) xs, d⟫_ℝ + ∑ j, U j * ⟪gradient (C.g j) xs, d⟫_ℝ = 0 := by
    have := congrArg (fun w => ⟪w, d⟫_ℝ) hsum
    simpa [inner_add_left, sum_inner, real_inner_smul_left] using this
  simp only [hd1, mul_zero, Finset.sum_const_zero, zero_add] at hin
  have hterm : ∀ j, U j * ⟪gradient (C.g j) xs, d⟫_ℝ ≤ 0 := by
    intro j
    by_cases hj : C.g j xs = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hU0 j) (hd2 j hj).le
    · rw [hUc j hj, zero_mul]
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).1 hin
  have hU : U = 0 := by
    funext j
    by_cases hj : C.g j xs = 0
    · have := hz j (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hd2 j hj).ne
    · exact hUc j hj
  refine ⟨?_, hU⟩
  subst hU
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at hsum
  funext i
  exact Fintype.linearIndependent_iff.1 hli L hsum i

lemma max_aux (M a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : M = max 1 (max a b)) :
    max M⁻¹ (max (M⁻¹ * a) (M⁻¹ * b)) = 1 := by
  have hMpos : 0 < M := by rw [hM]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have h : max M⁻¹ (max (M⁻¹ * a) (M⁻¹ * b)) = M⁻¹ * max 1 (max a b) := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.2 hMpos.le), mul_max_of_nonneg _ _ (inv_nonneg.2 hMpos.le),
      mul_one]
  rw [h, ← hM, inv_mul_cancel₀ hMpos.ne']

lemma forward {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1) (xs : E n)
    (hxs : xs ∈ C.feasible) (hM : C.MFCQ xs) (f : E n → ℝ) (hf : ContDiff ℝ 1 f)
    (hS : C.ScaledAKKT f xs) : C.IsKKT f xs := by
  obtain ⟨x, lam, mu, hx, hmu0, hmin, hres⟩ := hS
  set M : ℕ → ℝ := fun k => max 1 (max ‖lam k‖ ‖mu k‖) with hMdef
  have hM1 : ∀ k, 1 ≤ M k := fun k => le_max_left _ _
  have hMpos : ∀ k, 0 < M k := fun k => lt_of_lt_of_le one_pos (hM1 k)
  set a : ℕ → ℝ × (Fin m → ℝ) × (Fin p → ℝ) :=
    fun k => ((M k)⁻¹, (M k)⁻¹ • lam k, (M k)⁻¹ • mu k) with hadef
  have hanorm : ∀ k, ‖a k‖ = 1 := by
    intro k
    simp only [hadef, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hMpos k)]
    exact max_aux (M k) _ _ (norm_nonneg _) (norm_nonneg _) rfl
  have hmem : ∀ k, a k ∈ Metric.closedBall (0 : ℝ × (Fin m → ℝ) × (Fin p → ℝ)) 1 := by
    intro k; rw [mem_closedBall_zero_iff, hanorm]
  obtain ⟨a', -, φ, hφ, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hmem
  have hnorm' : ‖a'‖ = 1 := by
    have h1 : Tendsto (fun k => ‖(a ∘ φ) k‖) atTop (𝓝 ‖a'‖) := hlim.norm
    simp only [Function.comp, hanorm] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  obtain ⟨t, L, U⟩ := a'
  have ht : Tendsto (fun k => (M (φ k))⁻¹) atTop (𝓝 t) :=
    ((continuous_fst.tendsto _).comp hlim)
  have hU : Tendsto (fun k => (M (φ k))⁻¹ • mu (φ k)) atTop (𝓝 U) :=
    (((continuous_snd.comp continuous_snd).tendsto _).comp hlim)
  have ht0 : 0 ≤ t := ge_of_tendsto ht (Eventually.of_forall fun k => inv_nonneg.2 (hMpos _).le)
  have hUj : ∀ j, Tendsto (fun k => (M (φ k))⁻¹ * mu (φ k) j) atTop (𝓝 (U j)) := by
    intro j
    have := ((continuous_apply j).tendsto _).comp hU
    refine (tendsto_congr fun k => ?_).1 this
    simp
  have hU0 : ∀ j, 0 ≤ U j := fun j =>
    ge_of_tendsto (hUj j) (Eventually.of_forall fun k =>
      mul_nonneg (inv_nonneg.2 (hMpos _).le) (hmu0 _ j))
  have hgc : ∀ j, Continuous (C.g j) := fun j => (hC.2 j).continuous
  have hUc : ∀ j, C.g j xs ≠ 0 → U j = 0 := by
    intro j hj
    have hneg : 0 < -C.g j xs := by
      have := hxs.2 j
      exact neg_pos.2 (lt_of_le_of_ne this hj)
    have hg : Tendsto (fun k => -C.g j (x k)) atTop (𝓝 (-C.g j xs)) :=
      (((hgc j).tendsto xs).comp hx).neg
    have hev1 : ∀ᶠ k in atTop, -C.g j xs / 2 < -C.g j (x k) :=
      hg.eventually (lt_mem_nhds (by linarith))
    have hev2 : ∀ᶠ k in atTop, min (mu k j) (-C.g j (x k)) < -C.g j xs / 2 :=
      (hmin j).eventually (gt_mem_nhds (by linarith))
    have hmuj : Tendsto (fun k => mu k j) atTop (𝓝 0) := by
      refine (tendsto_congr' ?_).1 (hmin j)
      filter_upwards [hev1, hev2] with k h1 h2
      rcases min_choice (mu k j) (-C.g j (x k)) with h | h
      · exact h
      · rw [h] at h2; linarith
    have hsq : Tendsto (fun k => (M k)⁻¹ * mu k j) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => mul_nonneg (inv_nonneg.2 (hMpos k).le) (hmu0 k j))
        (fun k => ?_) hmuj
      have : (M k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hM1 k)
      nlinarith [hmu0 k j]
    exact tendsto_nhds_unique (hUj j) (hsq.comp hφ.tendsto_atTop)
  -- the limit equation
  have hgf := grad_cont f hf
  have hgh : ∀ i, Continuous (gradient (C.h i)) := fun i => grad_cont _ (hC.1 i)
  have hgg : ∀ j, Continuous (gradient (C.g j)) := fun j => grad_cont _ (hC.2 j)
  set Φ : (ℝ × (Fin m → ℝ) × (Fin p → ℝ)) × E n → E n := fun q =>
    q.1.1 • gradient f q.2 + ∑ i, q.1.2.1 i • gradient (C.h i) q.2 +
      ∑ j, q.1.2.2 j • gradient (C.g j) q.2 with hΦdef
  have hΦ : Continuous Φ := by
    simp only [hΦdef]
    fun_prop
  have hΦk : ∀ k, Φ (a k, x k) = (M k)⁻¹ • (gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k)) := by
    intro k
    simp only [hΦdef, hadef, smul_add, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  have hΦ0 : Tendsto (fun k => Φ (a k, x k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hΦk, norm_smul, Real.norm_eq_abs, abs_inv]
    refine (tendsto_congr fun k => ?_).1 hres
    rw [abs_of_pos (hMpos k)]
  have hΦlim : Tendsto (fun k => Φ (a (φ k), x (φ k))) atTop (𝓝 (Φ ((t, L, U), xs))) :=
    (hΦ.tendsto _).comp (hlim.prodMk_nhds (hx.comp hφ.tendsto_atTop))
  have heq : Φ ((t, L, U), xs) = 0 :=
    tendsto_nhds_unique hΦlim (hΦ0.comp hφ.tendsto_atTop)
  simp only [hΦdef] at heq
  rcases ht0.lt_or_eq with htpos | htz
  · refine ⟨t⁻¹ • L, t⁻¹ • U, fun j => ?_, fun j hj => ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.2 ht0) (hU0 j)
    · simp [hUc j hj]
    · have := congrArg (fun w => t⁻¹ • w) heq
      simp only [smul_add, Finset.smul_sum, smul_smul, smul_zero] at this
      rw [inv_mul_cancel₀ htpos.ne', one_smul] at this
      simpa [Pi.smul_apply, smul_eq_mul] using this
  · exfalso
    subst htz
    simp only [zero_smul, zero_add] at heq
    obtain ⟨hL0, hU0'⟩ := mfcq_no_dep C xs hM L U hU0 hUc heq
    subst hL0; subst hU0'
    simp [Prod.norm_def] at hnorm'

lemma dep {n m p : ℕ} (C : Constraints n m p) (xs : E n) (hM : ¬ C.MFCQ xs) :
    ∃ (L : Fin m → ℝ) (U : Fin p → ℝ), (∀ j, 0 ≤ U j) ∧ (∀ j, C.g j xs ≠ 0 → U j = 0) ∧
      (L ≠ 0 ∨ U ≠ 0) ∧ ∑ i, L i • gradient (C.h i) xs + ∑ j, U j • gradient (C.g j) xs = 0 := by
  by_cases hli : LinearIndependent ℝ (fun i => gradient (C.h i) xs)
  · set T : Set (Fin p → ℝ) :=
      {μ | (∀ j, 0 ≤ μ j) ∧ (∀ j, μ j * C.g j xs = 0) ∧ ∑ j, μ j = 1} with hTdef
    set G : (Fin p → ℝ) → E n := fun μ => ∑ j, μ j • gradient (C.g j) xs with hGdef
    have hGlin : IsLinearMap ℝ G :=
      ⟨fun a b => by simp [hGdef, add_smul, Finset.sum_add_distrib],
       fun c a => by simp [hGdef, Finset.smul_sum, smul_smul]⟩
    have hGc : Continuous G := by simp only [hGdef]; fun_prop
    have hTeq : T = ((⋂ j, {μ : Fin p → ℝ | 0 ≤ μ j}) ∩ (⋂ j, {μ : Fin p → ℝ | μ j * C.g j xs = 0}))
        ∩ {μ | ∑ j, μ j = 1} := by
      ext μ; simp [hTdef, Set.mem_iInter, and_assoc]
    have hTc : IsClosed T := by
      rw [hTeq]
      exact ((isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
        (isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const)).inter
        (isClosed_eq (by fun_prop) continuous_const)
    have hTsub : T ⊆ Metric.closedBall 0 1 := by
      intro μ hμ
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hμ.1 j), ← hμ.2.2]
      exact Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ j)
    have hTk : IsCompact T := (isCompact_closedBall 0 1).of_isClosed_subset hTc hTsub
    have hTcv : Convex ℝ T := by
      intro a ha b hb s t hs ht hst
      refine ⟨fun j => ?_, fun j => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := ha.1 j; have := hb.1 j; positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := ha.2.1 j; have h2 := hb.2.1 j
        linear_combination s * h1 + t * h2
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, ha.2.2, hb.2.2]
        linarith
    have hKc : IsCompact (G '' T) := hTk.image hGc
    have hKcv : Convex ℝ (G '' T) := hTcv.is_linear_image hGlin
    set V : Submodule ℝ (E n) := Submodule.span ℝ (Set.range fun i => gradient (C.h i) xs)
    have hVc : IsClosed (V : Set (E n)) := Submodule.closed_of_finiteDimensional _
    by_cases hdis : Disjoint (G '' T) (V : Set (E n))
    · exfalso
      apply hM
      refine ⟨hli, ?_⟩
      obtain ⟨F, u, v', hFu, huv, hFv⟩ :=
        geometric_hahn_banach_compact_closed hKcv hKc V.convex hVc hdis
      have hF0 : ∀ b ∈ V, F b = 0 := by
        intro b hb
        by_contra hne
        have hb' : ((v' - 1) / F b) • b ∈ V := V.smul_mem _ hb
        have := hFv _ hb'
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
        linarith
      have hv'neg : v' < 0 := by
        have := hFv 0 V.zero_mem
        simpa using this
      refine ⟨(InnerProductSpace.toDual ℝ (E n)).symm F, fun i => ?_, fun j hj => ?_⟩
      · rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
        exact hF0 _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
        have hmem : (Pi.single j 1 : Fin p → ℝ) ∈ T := by
          refine ⟨fun j' => ?_, fun j' => ?_, ?_⟩
          · by_cases h : j' = j
            · subst h; simp
            · simp [h]
          · by_cases h : j' = j
            · subst h; simp [hj]
            · simp [h]
          · simp
        have := hFu _ ⟨_, hmem, rfl⟩
        have hG : G (Pi.single j 1) = gradient (C.g j) xs := by
          simp [hGdef, Pi.single_apply]
        rw [hG] at this
        linarith
    · rw [Set.not_disjoint_iff] at hdis
      obtain ⟨k, ⟨μ, hμT, rfl⟩, hkV⟩ := hdis
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hkV
      refine ⟨-c, μ, hμT.1, fun j hj => (mul_eq_zero.1 (hμT.2.1 j)).resolve_right hj,
        Or.inr ?_, ?_⟩
      · intro h
        have := hμT.2.2
        rw [h] at this
        simp at this
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hc, hGdef]
        exact neg_add_cancel _
  · rw [Fintype.not_linearIndependent_iff] at hli
    obtain ⟨c, hc, i, hi⟩ := hli
    exact ⟨c, 0, fun _ => le_rfl, fun _ _ => rfl, Or.inl (fun h => hi (by rw [h]; rfl)),
      by simp [hc]⟩

lemma lin_grad {n : ℕ} (c z : E n) : gradient (fun z : E n => ⟪c, z⟫_ℝ) z = c := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ (E n) c).hasFDerivAt

lemma lin_C1 {n : ℕ} (c : E n) : ContDiff ℝ 1 (fun z : E n => ⟪c, z⟫_ℝ) :=
  (InnerProductSpace.toDual ℝ (E n) c).contDiff

lemma tend_aux {m p : ℕ} (L : Fin m → ℝ) (U : Fin p → ℝ) (hne : L ≠ 0 ∨ U ≠ 0) (r : ℝ) :
    Tendsto (fun k : ℕ => (max 1 (max ‖(k : ℝ) • L‖ ‖(k : ℝ) • U‖))⁻¹ * r) atTop (𝓝 0) := by
  have hc : 0 < max ‖L‖ ‖U‖ := by
    rcases hne with h | h
    · exact lt_max_of_lt_left (norm_pos_iff.2 h)
    · exact lt_max_of_lt_right (norm_pos_iff.2 h)
  have hle : ∀ k : ℕ, (k : ℝ) * max ‖L‖ ‖U‖ ≤ max 1 (max ‖(k : ℝ) • L‖ ‖(k : ℝ) • U‖) := by
    intro k
    rw [norm_smul, norm_smul, Real.norm_natCast, ← mul_max_of_nonneg _ _ (Nat.cast_nonneg k)]
    exact le_max_right _ _
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) * max ‖L‖ ‖U‖) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  have h2 := (tendsto_atTop_mono hle h1).inv_tendsto_atTop.mul_const r
  simpa using h2

end RRAux_StrictCQ_Scaled_eq_2_3_weakest

open StrictCQ.Scaled in
theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    (C.MFCQ xs ∨ C.activeCone xs = Set.univ) ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → C.ScaledAKKT f xs → C.IsKKT f xs := by
  open RRAux_StrictCQ_Scaled_eq_2_3_weakest in
  constructor
  · rintro (hM | hcone) f hf hS
    · exact forward C hC xs hxs hM f hf hS
    · have hmem : -gradient f xs ∈ C.activeCone xs := by rw [hcone]; trivial
      obtain ⟨lam, mu, h0, hc, heq⟩ := hmem
      refine ⟨lam, mu, h0, hc, ?_⟩
      rw [add_assoc, ← heq, add_neg_cancel]
  · intro H
    by_contra hneg
    rw [not_or] at hneg
    obtain ⟨wv, hwv⟩ : ∃ w, w ∉ C.activeCone xs := by
      by_contra h
      push Not at h
      exact hneg.2 (Set.eq_univ_of_forall h)
    obtain ⟨L, U, hU0, hUc, hne, hsum⟩ := dep C xs hneg.1
    have hgf : ∀ z, gradient (fun z : EuclideanSpace ℝ (Fin n) => ⟪-wv, z⟫_ℝ) z = -wv :=
      fun z => lin_grad _ z
    have hres : ∀ k : ℕ, gradient (fun z : EuclideanSpace ℝ (Fin n) => ⟪-wv, z⟫_ℝ) xs +
        ∑ i, ((k : ℝ) • L) i • gradient (C.h i) xs + ∑ j, ((k : ℝ) • U) j • gradient (C.g j) xs
        = -wv := by
      intro k
      have : ∑ i, ((k : ℝ) • L) i • gradient (C.h i) xs + ∑ j, ((k : ℝ) • U) j • gradient (C.g j) xs
          = (k : ℝ) • (∑ i, L i • gradient (C.h i) xs + ∑ j, U j • gradient (C.g j) xs) := by
        simp [smul_add, Finset.smul_sum, smul_smul]
      rw [hgf, add_assoc, this, hsum, smul_zero, add_zero]
    have hK := H _ (lin_C1 (-wv)) ⟨fun _ => xs, fun k => (k : ℝ) • L, fun k => (k : ℝ) • U,
      tendsto_const_nhds, fun k j => mul_nonneg (Nat.cast_nonneg k) (hU0 j), fun j => ?_, ?_⟩
    · obtain ⟨lam, mu, h0, hc, heq⟩ := hK
      apply hwv
      refine ⟨lam, mu, h0, hc, ?_⟩
      rw [hgf, add_assoc, neg_add_eq_zero] at heq
      exact heq
    · refine tendsto_const_nhds.congr fun k => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hj : C.g j xs = 0
      · rw [hj, neg_zero, min_eq_right (mul_nonneg (Nat.cast_nonneg k) (hU0 j))]
      · rw [hUc j hj, mul_zero, min_eq_left (neg_nonneg.2 (hxs.2 j))]
    · simp only [hres]
      exact tend_aux L U hne _

#print axioms solution
