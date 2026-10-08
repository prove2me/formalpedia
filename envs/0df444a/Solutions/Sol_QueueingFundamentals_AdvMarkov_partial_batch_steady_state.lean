-- Prove2me | solution 1 for QueueingFundamentals.AdvMarkov.partial_batch_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:34:17.472387+00:00
-- url     : https://prove2.me/submissions/16434787-ab2d-4d83-bad7-40640c961d39

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_BulkService

open Filter Topology Polynomial

namespace QueueingFundamentals.AdvMarkov

noncomputable def pbShift : Module.End ℂ (ℕ → ℂ) where
  toFun := fun e n => e (n+1)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

lemma pbShift_pow_apply (k : ℕ) (e : ℕ → ℂ) (n : ℕ) : (pbShift ^ k) e n = e (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    show (pbShift ^ k) e (n+1) = _
    rw [ih]; congr 1; omega

lemma pb_factor_apply (s : ℂ) (w : ℕ → ℂ) (n : ℕ) :
    (pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s) w n = w (n+1) - s * w n := by
  simp [Module.algebraMap_end_apply]
  rfl

lemma pb_tend (M : List ℂ) (e : ℕ → ℂ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto ((M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e)
      atTop (𝓝 0) := by
  induction M using List.rec with
  | nil => simpa using he
  | cons s M ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    have : (fun n => ((pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)
        ((M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e)) n) =
        fun n => ((M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e) (n+1)
          - s * ((M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e) n := by
      funext n; exact pb_factor_apply _ _ n
    rw [show ((pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)
        ((M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e)) =
        fun n => ((pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)
        ((M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e)) n from rfl, this]
    have h1 := (tendsto_add_atTop_iff_nat 1).mpr ih
    have h2 := ih.const_mul s
    simpa using h1.sub h2

lemma pb_kill (M : List ℂ) (hM : ∀ s ∈ M, 1 ≤ ‖s‖) (e : ℕ → ℂ)
    (he : Tendsto e atTop (𝓝 0))
    (h : (M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e = 0) :
    e = 0 := by
  induction M using List.rec generalizing e with
  | nil => simpa using h
  | cons s M ih =>
    apply ih (fun t ht => hM t (List.mem_cons_of_mem s ht)) e he
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply] at h
    set w := (M.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e with hw
    have hwt : Tendsto w atTop (𝓝 0) := pb_tend M e he
    have hrec : ∀ n, w (n+1) = s * w n := by
      intro n
      have := congrFun h n
      rw [pb_factor_apply] at this
      simp at this
      linear_combination this
    have hs := hM s (List.mem_cons_self)
    have hge : ∀ n, ‖w 0‖ ≤ ‖w n‖ := by
      intro n
      induction n with
      | zero => exact le_refl _
      | succ n ihn =>
        rw [hrec, norm_mul]
        calc ‖w 0‖ ≤ ‖w n‖ := ihn
          _ = 1 * ‖w n‖ := (one_mul _).symm
          _ ≤ ‖s‖ * ‖w n‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    have hw0 : w 0 = 0 := by
      have hn : Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := by
        simpa using hwt.norm
      have : ‖w 0‖ ≤ 0 := ge_of_tendsto' hn (fun n => hge n)
      exact norm_le_zero_iff.mp this
    funext n
    induction n with
    | zero => exact hw0
    | succ n ihn => rw [hrec, ihn]; simp


/-- `G r = μ r (1 + r + ⋯ + r^{K-1})`. -/
noncomputable def pbG (mu : ℝ) (K : ℕ) (r : ℝ) : ℝ := mu * r * ∑ i ∈ Finset.range K, r ^ i

lemma pb_factor {R : Type*} [CommRing R] (lam mu r : R) (K : ℕ) :
    mu * r ^ (K + 1) - (lam + mu) * r + lam = (1 - r) * (lam - mu * r * ∑ i ∈ Finset.range K, r ^ i) := by
  have h := geom_sum_mul r K
  linear_combination (-(mu * r)) * h

lemma pbG_strictMono (mu : ℝ) (hmu : 0 < mu) (K : ℕ) (hK : 1 ≤ K) (x y : ℝ) (hx : 0 ≤ x)
    (hxy : x < y) : pbG mu K x < pbG mu K y := by
  unfold pbG
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have h1 : ∑ i ∈ Finset.range K, x ^ i ≤ ∑ i ∈ Finset.range K, y ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hx hxy.le i)
  have h0 : 0 < ∑ i ∈ Finset.range K, y ^ i :=
    Finset.sum_pos (fun i _ => pow_pos hy i) (by simp; omega)
  have h0' : 0 ≤ ∑ i ∈ Finset.range K, x ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hx i)
  calc mu * x * ∑ i ∈ Finset.range K, x ^ i ≤ mu * x * ∑ i ∈ Finset.range K, y ^ i :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ < mu * y * ∑ i ∈ Finset.range K, y ^ i := by
        apply mul_lt_mul_of_pos_right _ h0
        exact mul_lt_mul_of_pos_left hxy hmu

lemma pb_sum_Icc (r : ℝ) (K : ℕ) : ∑ k ∈ Finset.Icc 1 K, r ^ k = r * ∑ i ∈ Finset.range K, r ^ i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    ring

/-- Location of the complex roots inside the unit disc. -/
lemma pb_location (lam mu : ℝ) (K : ℕ) (hlam : 0 < lam) (hmu : 0 < mu) (hK : 1 ≤ K)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0:ℝ) 1) (hroot : mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0)
    (s : ℂ) (hs : ‖s‖ < 1)
    (hsr : (mu:ℂ) * s ^ (K + 1) - ((lam:ℂ) + mu) * s + lam = 0) : s = r0 := by
  set t := ‖s‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg s
  have hG0 : pbG mu K r0 = lam := by
    rw [pb_factor] at hroot
    have : (1 - r0) ≠ 0 := by linarith [hr0.2]
    unfold pbG
    have := (mul_eq_zero.mp hroot).resolve_left this
    linarith
  -- step A : r0 ≤ t
  have hA : r0 ≤ t := by
    by_contra hlt
    push_neg at hlt
    have hs1 : (1 - s) ≠ 0 := by
      intro h
      have : s = 1 := by linear_combination -h
      rw [ht, this] at hs; simp at hs
    rw [pb_factor] at hsr
    have hl := (mul_eq_zero.mp hsr).resolve_left hs1
    have heq : (lam:ℂ) = mu * s * ∑ i ∈ Finset.range K, s ^ i := by linear_combination hl
    have hn : lam ≤ pbG mu K t := by
      have h1 : ‖(lam:ℂ)‖ = lam := by simp [abs_of_pos hlam]
      rw [← h1, heq, norm_mul, norm_mul]
      unfold pbG
      have h2 : ‖((mu:ℝ):ℂ)‖ = mu := by simp [abs_of_pos hmu]
      rw [h2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      simp only [norm_pow]; rfl
    have := pbG_strictMono mu hmu K hK t r0 ht0 hlt
    linarith
  -- step B : norm identity
  have hB : (mu * t ^ (K + 1)) ^ 2 = (lam + mu) ^ 2 * t ^ 2 - 2 * lam * (lam + mu) * s.re + lam ^ 2 := by
    have e1 : (mu:ℂ) * s ^ (K + 1) = ((lam + mu : ℝ) : ℂ) * s - (lam : ℝ) := by
      push_cast; linear_combination hsr
    have e2 : ‖(mu:ℂ) * s ^ (K + 1)‖ ^ 2 = ‖((lam + mu : ℝ) : ℂ) * s - (lam : ℝ)‖ ^ 2 := by rw [e1]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmu] at e2
    rw [e2, Complex.sq_norm, Complex.normSq_apply, ht, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hre : s.re ≤ t := le_trans (le_abs_self _) (Complex.abs_re_le_norm s)
  have htn : t ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [ht, Complex.sq_norm, Complex.normSq_apply]; ring
  have hlm : 0 < lam * (lam + mu) := by positivity
  have hft : mu * t ^ (K + 1) - (lam + mu) * t + lam = (1 - t) * (lam - pbG mu K t) := by
    rw [pb_factor]; rfl
  rcases eq_or_lt_of_le hA with heq | hlt
  · -- t = r0
    have hf : mu * t ^ (K + 1) = (lam + mu) * t - lam := by rw [← heq]; linarith
    rw [hf] at hB
    have hres : s.re = t := by nlinarith
    have him : s.im = 0 := by nlinarith
    apply Complex.ext
    · simp [hres, ← heq]
    · simp [him]
  · exfalso
    have hGt := pbG_strictMono mu hmu K hK r0 t hr0.1.le hlt
    have h1t : 0 < 1 - t := by linarith
    have hneg : mu * t ^ (K + 1) - (lam + mu) * t + lam < 0 := by
      rw [hft]; nlinarith
    have hpos : 0 ≤ mu * t ^ (K + 1) := by positivity
    nlinarith


lemma pbShift_apply (e : ℕ → ℂ) (n : ℕ) : pbShift e n = e (n + 1) := rfl

lemma pb_recur_unique (lam mu : ℝ) (K : ℕ) (hlam : 0 < lam) (hmu : 0 < mu) (hK : 1 ≤ K)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0:ℝ) 1) (hroot : mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0)
    (p : ℕ → ℝ) (hpt : Tendsto p atTop (𝓝 0))
    (hrec : ∀ m : ℕ, mu * p (m + K + 1) - (lam + mu) * p (m + 1) + lam * p m = 0) :
    ∀ n, p n = p 0 * r0 ^ n := by
  set F : ℂ[X] := C (mu:ℂ) * X ^ (K + 1) - C ((lam:ℂ) + mu) * X + C (lam:ℂ) with hF
  have hFeval : ∀ z : ℂ, F.eval z = (mu:ℂ) * z ^ (K + 1) - ((lam:ℂ) + mu) * z + lam := by
    intro z; simp [hF]
  have hFr : F.IsRoot (r0:ℂ) := by
    rw [IsRoot, hFeval]
    exact_mod_cast hroot
  set g := F /ₘ (X - C (r0:ℂ)) with hg
  have hFg : (X - C (r0:ℂ)) * g = F := mul_divByMonic_eq_iff_isRoot.mpr hFr
  have hF0 : F ≠ 0 := by
    intro h
    have := hFeval 0
    rw [h] at this
    simp at this
    exact hlam.ne' (by exact_mod_cast this.symm)
  have hg0 : g ≠ 0 := by
    intro h; rw [h, mul_zero] at hFg; exact hF0 hFg.symm
  -- simple root
  have hG0 : lam = mu * ∑ i ∈ Finset.range K, r0 ^ (i + 1) := by
    rw [pb_factor] at hroot
    have : (1 - r0) ≠ 0 := by linarith [hr0.2]
    have := (mul_eq_zero.mp hroot).resolve_left this
    rw [Finset.mul_sum] at this ⊢
    have e : ∑ i ∈ Finset.range K, mu * r0 * r0 ^ i = ∑ i ∈ Finset.range K, mu * r0 ^ (i + 1) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    linarith
  have hneg : ((K:ℝ) + 1) * mu * r0 ^ K - (lam + mu) < 0 := by
    have h1 : ∑ i ∈ Finset.range K, r0 ^ K ≤ ∑ i ∈ Finset.range K, r0 ^ (i + 1) :=
      Finset.sum_le_sum (fun i hi => pow_le_pow_of_le_one hr0.1.le hr0.2.le
        (by simp at hi; omega))
    simp at h1
    have h2 : r0 ^ K < 1 := pow_lt_one₀ hr0.1.le hr0.2 (by omega)
    rw [hG0]
    nlinarith
  have hgr : g.eval (r0:ℂ) ≠ 0 := by
    intro h
    have hd := congrArg (fun q => (derivative q).eval (r0:ℂ)) hFg
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, h, zero_add] at hd
    have : (derivative F).eval (r0:ℂ) = (((K:ℝ) + 1) * mu * r0 ^ K - (lam + mu) : ℝ) := by
      simp [hF]; push_cast; ring
    rw [this] at hd
    have := hneg.ne
    apply this
    exact_mod_cast hd.symm
  -- the sequence
  set pc : ℕ → ℂ := fun n => (p n : ℂ) with hpc
  have hS : (aeval pbShift F) pc = 0 := by
    funext m
    simp only [hF, map_sub, map_add, map_mul, aeval_C, aeval_X, map_pow, LinearMap.sub_apply,
      LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, pbShift_pow_apply, pbShift_apply, Pi.zero_apply,
      Algebra.algebraMap_self, RingHom.id_apply, hpc]
    have := hrec m
    rw [show m + (K + 1) = m + K + 1 by ring]
    have h2 : ((mu * p (m + K + 1) - (lam + mu) * p (m + 1) + lam * p m : ℝ) : ℂ) = 0 := by
      rw [this]; simp
    push_cast at h2
    linear_combination h2
  set e := aeval pbShift (X - C (r0:ℂ)) pc with he
  have he_apply : ∀ m, e m = pc (m + 1) - r0 * pc m := by
    intro m
    simp [he, pbShift_apply, Module.algebraMap_end_apply]
  have hge : (aeval pbShift g) e = 0 := by
    rw [he, ← Module.End.mul_apply, ← map_mul, mul_comm, hFg, hS]
  have het : Tendsto e atTop (𝓝 0) := by
    have hpc : Tendsto pc atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp hpt
      simp only [Complex.ofReal_zero] at this
      exact this
    have : e = fun m => pc (m + 1) - r0 * pc m := funext he_apply
    rw [this]
    have h1 := (tendsto_add_atTop_iff_nat 1).mpr hpc
    have h2 := hpc.const_mul (r0:ℂ)
    simpa using h1.sub h2
  -- factor g
  set L := g.roots.toList with hL
  have hgprod : C g.leadingCoeff * (L.map (fun a => X - C a)).prod = g := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g) IsAlgClosed.card_roots_eq_natDegree
    rw [← Multiset.coe_toList g.roots, Multiset.map_coe, Multiset.prod_coe] at this
    exact this
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hprod : (L.map (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s)).prod e = 0 := by
    rw [← hgprod, map_mul, aeval_C, map_list_prod, List.map_map, Module.End.mul_apply,
      Module.algebraMap_end_apply] at hge
    have hm : (aeval pbShift ∘ fun a => X - C a) =
        (fun s => pbShift - algebraMap ℂ (Module.End ℂ (ℕ → ℂ)) s) := by
      funext a; simp
    rw [hm] at hge
    exact (smul_eq_zero.mp hge).resolve_left hlc
  have hroots : ∀ s ∈ L, 1 ≤ ‖s‖ := by
    intro s hs
    rw [hL, Multiset.mem_toList] at hs
    have hgs : g.IsRoot s := (mem_roots hg0).mp hs
    by_contra hlt
    push_neg at hlt
    have hFs : F.eval s = 0 := by
      rw [← hFg, eval_mul, hgs.eq_zero, mul_zero]
    rw [hFeval] at hFs
    have := pb_location lam mu K hlam hmu hK r0 hr0 hroot s hlt hFs
    rw [this] at hgs
    exact hgr hgs.eq_zero
  have he0 := pb_kill L hroots e het hprod
  have hstep : ∀ m, p (m + 1) = r0 * p m := by
    intro m
    have := he_apply m
    rw [he0] at this
    simp [hpc] at this
    have h2 : ((p (m+1) : ℝ) : ℂ) = ((r0 * p m : ℝ) : ℂ) := by
      push_cast; linear_combination -this
    exact_mod_cast h2
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [hstep, ih]; ring


theorem pb_core (lam mu : ℝ) (K : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hK : 1 ≤ K) (hstab : lam < (K : ℝ) * mu) :
    (∃! r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0) ∧
      ∀ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 → mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0 →
        IsPartialBatchSteadyState lam mu K (fun n : ℕ => (1 - r0) * r0 ^ n) ∧
          ∀ p : ℕ → ℝ, IsPartialBatchSteadyState lam mu K p →
            ∀ n : ℕ, p n = (1 - r0) * r0 ^ n := by
  have hroot_iff : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      (mu * r ^ (K + 1) - (lam + mu) * r + lam = 0 ↔ pbG mu K r = lam) := by
    intro r hr
    rw [pb_factor]
    have : (1 - r) ≠ 0 := by linarith [hr.2]
    unfold pbG
    constructor
    · intro h; have := (mul_eq_zero.mp h).resolve_left this; linarith
    · intro h; rw [h, sub_self, mul_zero]
  refine ⟨?_, ?_⟩
  · have hcont : ContinuousOn (pbG mu K) (Set.Icc 0 1) := by
      unfold pbG; fun_prop
    have h0 : pbG mu K 0 = 0 := by simp [pbG]
    have h1 : pbG mu K 1 = K * mu := by simp [pbG]; ring
    obtain ⟨r, hr, hrG⟩ := intermediate_value_Ioo (zero_le_one) hcont
      ⟨by rw [h0]; exact hlam, by rw [h1]; exact hstab⟩
    refine ⟨r, ⟨hr, (hroot_iff r hr).mpr hrG⟩, ?_⟩
    rintro y ⟨hy, hyr⟩
    have hyG := (hroot_iff y hy).mp hyr
    rcases lt_trichotomy y r with h | h | h
    · have := pbG_strictMono mu hmu K hK y r hy.1.le h; linarith
    · exact h
    · have := pbG_strictMono mu hmu K hK r y hr.1.le h; linarith
  · intro r0 hr0 hroot
    have hG := (hroot_iff r0 hr0).mp hroot
    have h1r : (1 - r0) ≠ 0 := by linarith [hr0.2]
    refine ⟨⟨fun n => mul_nonneg (by linarith [hr0.2]) (pow_nonneg hr0.1.le n), ?_, ?_, ?_⟩, ?_⟩
    · have := (hasSum_geometric_of_lt_one hr0.1.le hr0.2).mul_left (1 - r0)
      rwa [mul_inv_cancel₀ h1r] at this
    · intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [show m + 1 + K = m + (K + 1) by ring, pow_add, pow_succ]
      linear_combination (-(1 - r0) * r0 ^ m) * hroot
    · have : ∑ k ∈ Finset.Icc 1 K, (1 - r0) * r0 ^ k =
          (1 - r0) * (r0 * ∑ i ∈ Finset.range K, r0 ^ i) := by
        rw [← Finset.mul_sum, pb_sum_Icc]
      rw [this]
      unfold pbG at hG
      linear_combination (-(1 - r0)) * hG
    · intro p hp
      have hpt : Tendsto p atTop (𝓝 0) := hp.2.1.summable.tendsto_atTop_zero
      have hrec : ∀ m : ℕ, mu * p (m + K + 1) - (lam + mu) * p (m + 1) + lam * p m = 0 := by
        intro m
        have := hp.2.2.1 (m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at this
        rw [show m + K + 1 = m + 1 + K by ring]
        linarith
      have hgeo := pb_recur_unique lam mu K hlam hmu hK r0 hr0 hroot p hpt hrec
      have hpf : p = fun n => p 0 * r0 ^ n := funext hgeo
      have hs := (hasSum_geometric_of_lt_one hr0.1.le hr0.2).mul_left (p 0)
      have h1 := hp.2.1
      rw [hpf] at h1
      have := h1.unique hs
      have hp0 : p 0 = 1 - r0 := by
        field_simp at this
        linarith
      intro n
      rw [hgeo n, hp0]

end QueueingFundamentals.AdvMarkov

open QueueingFundamentals.AdvMarkov


theorem solution (lam mu : ℝ) (K : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hK : 1 ≤ K) (hstab : lam < (K : ℝ) * mu) :
    (∃! r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0) ∧
      ∀ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 → mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0 →
        IsPartialBatchSteadyState lam mu K (fun n : ℕ => (1 - r0) * r0 ^ n) ∧
          ∀ p : ℕ → ℝ, IsPartialBatchSteadyState lam mu K p →
            ∀ n : ℕ, p n = (1 - r0) * r0 ^ n := by
  exact pb_core lam mu K hlam hmu hK hstab
