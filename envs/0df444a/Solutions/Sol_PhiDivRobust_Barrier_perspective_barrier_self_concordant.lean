-- Prove2me | solution 1 for PhiDivRobust.Barrier.perspective_barrier_self_concordant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T09:11:37.823608+00:00
-- url     : https://prove2.me/submissions/37e14974-6e88-4bd5-bd3d-f937d42ee283

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_IsSelfConcordant
import Definitions.Def_PhiDivRobust_Barrier_perspective
import Definitions.Def_PhiDivRobust_Barrier_logBarrier



namespace PhiDivRobust.Barrier

open Filter Topology

theorem pdb_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (U : Set E) (hU : IsOpen U) (n : ℕ) (hg : ContDiffOn ℝ n g U)
    (x : E) (hx : x ∈ U) (h : E) :
    iteratedFDeriv ℝ n g x (fun _ => h) = iteratedDeriv n (fun t : ℝ => g (x + t • h)) 0 := by
  set ℓ : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h with hℓ
  set G : E → ℝ := fun z => g (z + x) with hG
  set U' : Set E := (fun z => z + x) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
  have hGc : ContDiffOn ℝ n G U' := by
    refine hg.comp (contDiff_id.add contDiff_const).contDiffOn ?_
    intro z hz; exact hz
  have h0 : ℓ 0 ∈ U' := by simp [hU', hℓ, hx]
  have hpre : IsOpen (ℓ ⁻¹' U') := hU'o.preimage ℓ.continuous
  have key := ℓ.iteratedFDerivWithin_comp_right hGc hU'o.uniqueDiffOn hpre.uniqueDiffOn h0
    (i := n) le_rfl
  have e1 : iteratedFDerivWithin ℝ n (G ∘ ℓ) (ℓ ⁻¹' U') 0 = iteratedFDeriv ℝ n (G ∘ ℓ) 0 :=
    iteratedFDerivWithin_of_isOpen n hpre (by simpa using h0)
  have e2 : iteratedFDerivWithin ℝ n G U' (ℓ 0) = iteratedFDeriv ℝ n G (ℓ 0) :=
    iteratedFDerivWithin_of_isOpen n hU'o h0
  rw [e1, e2] at key
  have hfun : (fun t : ℝ => g (x + t • h)) = G ∘ ℓ := by
    funext t; simp [hG, hℓ, add_comm]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, key]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have : ℓ 0 = 0 := by simp
  rw [this, hG, iteratedFDeriv_comp_add_right]
  simp [hℓ]

theorem pdb_iter2 (φ φ1 : ℝ → ℝ) (c : ℝ) (V : Set ℝ) (hV : IsOpen V) (t0 : ℝ) (ht0 : t0 ∈ V)
    (h1 : ∀ t ∈ V, HasDerivAt φ (φ1 t) t) (h2 : HasDerivAt φ1 c t0) :
    iteratedDeriv 2 φ t0 = c := by
  have hEq : deriv φ =ᶠ[𝓝 t0] φ1 := by
    filter_upwards [hV.mem_nhds ht0] with t ht
    exact (h1 t ht).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hEq.deriv_eq, h2.deriv]

theorem pdb_iter3 (φ φ1 φ2 : ℝ → ℝ) (c : ℝ) (V : Set ℝ) (hV : IsOpen V) (t0 : ℝ) (ht0 : t0 ∈ V)
    (h1 : ∀ t ∈ V, HasDerivAt φ (φ1 t) t) (h2 : ∀ t ∈ V, HasDerivAt φ1 (φ2 t) t)
    (h3 : HasDerivAt φ2 c t0) :
    iteratedDeriv 3 φ t0 = c := by
  have hEq : iteratedDeriv 2 φ =ᶠ[𝓝 t0] φ2 := by
    filter_upwards [hV.mem_nhds ht0] with t ht
    exact pdb_iter2 φ φ1 (φ2 t) V hV t ht h1 (h2 t ht)
  rw [iteratedDeriv_succ, hEq.deriv_eq, h3.deriv]


theorem pdb_U_open : IsOpen {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2} :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

theorem pdb_persp_contDiffOn (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (perspective f) {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2} := by
  have hd : ContDiffOn ℝ 3 (fun q : ℝ × ℝ => q.1 / q.2) {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2} :=
    contDiffOn_fst.div contDiffOn_snd (fun q hq => hq.2.ne')
  have hc : ContDiffOn ℝ 3 (fun q : ℝ × ℝ => f (q.1 / q.2)) {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2} :=
    hf.comp hd (fun q hq => div_pos hq.1 hq.2)
  exact contDiffOn_snd.mul hc

theorem pdb_V_open (s y h1 h2 : ℝ) : IsOpen {t : ℝ | 0 < s + t * h1 ∧ 0 < y + t * h2} :=
  (isOpen_lt continuous_const (by fun_prop : Continuous fun t : ℝ => s + t * h1)).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous fun t : ℝ => y + t * h2))

theorem pdb_u_deriv (s y h1 h2 t : ℝ) (hY : 0 < y + t * h2) :
    HasDerivAt (fun t => (s + t * h1) / (y + t * h2))
      ((h1 - (s + t * h1) / (y + t * h2) * h2) / (y + t * h2)) t := by
  have hS : HasDerivAt (fun t => s + t * h1) h1 t := by
    simpa using ((hasDerivAt_id t).mul_const h1).const_add s
  have hY' : HasDerivAt (fun t => y + t * h2) h2 t := by
    simpa using ((hasDerivAt_id t).mul_const h2).const_add y
  refine (hS.div hY' hY.ne').congr_deriv ?_
  field_simp

theorem pdb_comp_deriv (k : ℝ → ℝ) (s y h1 h2 t : ℝ) (hY : 0 < y + t * h2)
    (hk : DifferentiableAt ℝ k ((s + t * h1) / (y + t * h2))) :
    HasDerivAt (fun t => k ((s + t * h1) / (y + t * h2)))
      (deriv k ((s + t * h1) / (y + t * h2)) *
        ((h1 - (s + t * h1) / (y + t * h2) * h2) / (y + t * h2))) t :=
  hk.hasDerivAt.comp t (pdb_u_deriv s y h1 h2 t hY)

theorem pdb_phi1 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (s y h1 h2 t : ℝ)
    (ht : 0 < s + t * h1 ∧ 0 < y + t * h2) :
    HasDerivAt (fun t => (y + t * h2) * f ((s + t * h1) / (y + t * h2)))
      (h2 * f ((s + t * h1) / (y + t * h2)) + deriv f ((s + t * h1) / (y + t * h2)) *
        (h1 - (s + t * h1) / (y + t * h2) * h2)) t := by
  have hu : 0 < (s + t * h1) / (y + t * h2) := div_pos ht.1 ht.2
  have hfd : DifferentiableAt ℝ f ((s + t * h1) / (y + t * h2)) :=
    (hf.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hu)
  have hY' : HasDerivAt (fun t => y + t * h2) h2 t := by
    simpa using ((hasDerivAt_id t).mul_const h2).const_add y
  refine (hY'.mul (pdb_comp_deriv f s y h1 h2 t ht.2 hfd)).congr_deriv ?_
  have := ht.2.ne'
  have : y + h2 * t ≠ 0 := by rw [mul_comm]; exact ht.2.ne'
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.add_apply, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one]
  try generalize deriv (deriv (deriv f)) ((s + t * h1) / (y + t * h2)) = A3
  try generalize deriv (deriv f) ((s + t * h1) / (y + t * h2)) = A2
  try generalize deriv f ((s + t * h1) / (y + t * h2)) = A1
  have hYn := ht.2.ne'
  generalize y + t * h2 = Y at hYn ⊢
  generalize s + t * h1 = S
  field_simp

theorem pdb_phi2 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (s y h1 h2 t : ℝ)
    (ht : 0 < s + t * h1 ∧ 0 < y + t * h2) :
    HasDerivAt (fun t => h2 * f ((s + t * h1) / (y + t * h2)) +
        deriv f ((s + t * h1) / (y + t * h2)) * (h1 - (s + t * h1) / (y + t * h2) * h2))
      (deriv (deriv f) ((s + t * h1) / (y + t * h2)) *
        (h1 - (s + t * h1) / (y + t * h2) * h2) ^ 2 / (y + t * h2)) t := by
  have hu : 0 < (s + t * h1) / (y + t * h2) := div_pos ht.1 ht.2
  have hfd : DifferentiableAt ℝ f ((s + t * h1) / (y + t * h2)) :=
    (hf.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hu)
  have hf1 : ContDiffOn ℝ 2 (deriv f) (Set.Ioi 0) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hfd2 : DifferentiableAt ℝ (deriv f) ((s + t * h1) / (y + t * h2)) :=
    (hf1.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hu)
  have A := pdb_comp_deriv f s y h1 h2 t ht.2 hfd
  have B := pdb_comp_deriv (deriv f) s y h1 h2 t ht.2 hfd2
  have C := pdb_u_deriv s y h1 h2 t ht.2
  refine ((A.const_mul h2).add (B.mul ((C.mul_const h2).const_sub h1))).congr_deriv ?_
  have := ht.2.ne'
  have : y + h2 * t ≠ 0 := by rw [mul_comm]; exact ht.2.ne'
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.add_apply, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one]
  try generalize deriv (deriv (deriv f)) ((s + t * h1) / (y + t * h2)) = A3
  try generalize deriv (deriv f) ((s + t * h1) / (y + t * h2)) = A2
  try generalize deriv f ((s + t * h1) / (y + t * h2)) = A1
  have hYn := ht.2.ne'
  generalize y + t * h2 = Y at hYn ⊢
  generalize s + t * h1 = S
  field_simp
  ring

theorem pdb_phi3 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (s y h1 h2 t : ℝ)
    (ht : 0 < s + t * h1 ∧ 0 < y + t * h2) :
    HasDerivAt (fun t => deriv (deriv f) ((s + t * h1) / (y + t * h2)) *
        (h1 - (s + t * h1) / (y + t * h2) * h2) ^ 2 / (y + t * h2))
      (deriv (deriv (deriv f)) ((s + t * h1) / (y + t * h2)) *
          (h1 - (s + t * h1) / (y + t * h2) * h2) ^ 3 / (y + t * h2) ^ 2
        - 3 * deriv (deriv f) ((s + t * h1) / (y + t * h2)) * h2 *
          (h1 - (s + t * h1) / (y + t * h2) * h2) ^ 2 / (y + t * h2) ^ 2) t := by
  have hu : 0 < (s + t * h1) / (y + t * h2) := div_pos ht.1 ht.2
  have hf1 : ContDiffOn ℝ 2 (deriv f) (Set.Ioi 0) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hf2 : ContDiffOn ℝ 1 (deriv (deriv f)) (Set.Ioi 0) :=
    hf1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hfd3 : DifferentiableAt ℝ (deriv (deriv f)) ((s + t * h1) / (y + t * h2)) :=
    (hf2.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hu)
  have B := pdb_comp_deriv (deriv (deriv f)) s y h1 h2 t ht.2 hfd3
  have C := pdb_u_deriv s y h1 h2 t ht.2
  have hY' : HasDerivAt (fun t => y + t * h2) h2 t := by
    simpa using ((hasDerivAt_id t).mul_const h2).const_add y
  refine ((B.mul (((C.mul_const h2).const_sub h1).pow 2)).div hY' ht.2.ne').congr_deriv ?_
  have := ht.2.ne'
  have : y + h2 * t ≠ 0 := by rw [mul_comm]; exact ht.2.ne'
  try simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.add_apply, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one]
  try generalize deriv (deriv (deriv f)) ((s + t * h1) / (y + t * h2)) = A3
  try generalize deriv (deriv f) ((s + t * h1) / (y + t * h2)) = A2
  try generalize deriv f ((s + t * h1) / (y + t * h2)) = A1
  have hYn := ht.2.ne'
  generalize y + t * h2 = Y at hYn ⊢
  generalize s + t * h1 = S
  field_simp
  ring

theorem pdb_phi_eq (f : ℝ → ℝ) (s y h1 h2 : ℝ) :
    (fun t : ℝ => perspective f ((s, y) + t • (h1, h2))) =
      fun t => (y + t * h2) * f ((s + t * h1) / (y + t * h2)) := by
  funext t; simp [perspective, mul_comm]

theorem pdb_iter2f (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

theorem pdb_iter3f (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, pdb_iter2f]

theorem pdb_D2 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) * (h.1 - s / y * h.2) ^ 2 / y := by
  obtain ⟨h1, h2⟩ := h
  rw [pdb_line _ _ pdb_U_open 2 ((pdb_persp_contDiffOn f hf).of_le (by norm_num)) (s, y)
    ⟨hs, hy⟩, pdb_phi_eq]
  have := pdb_iter2 _ _ _ _ (pdb_V_open s y h1 h2) 0 (by simp [hs, hy])
    (fun t ht => pdb_phi1 f hf s y h1 h2 t ht) (pdb_phi2 f hf s y h1 h2 0 (by simp [hs, hy]))
  rw [this, pdb_iter2f]
  simp

theorem pdb_D3 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 3 f (s / y) * (h.1 - s / y * h.2) ^ 3 / y ^ 2
        - 3 * iteratedDeriv 2 f (s / y) * h.2 * (h.1 - s / y * h.2) ^ 2 / y ^ 2 := by
  obtain ⟨h1, h2⟩ := h
  rw [pdb_line _ _ pdb_U_open 3 (pdb_persp_contDiffOn f hf) (s, y) ⟨hs, hy⟩, pdb_phi_eq]
  have := pdb_iter3 _ _ (fun t => deriv (deriv f) ((s + t * h1) / (y + t * h2)) *
        (h1 - (s + t * h1) / (y + t * h2) * h2) ^ 2 / (y + t * h2)) _
    _ (pdb_V_open s y h1 h2) 0 (by simp [hs, hy])
    (fun t ht => pdb_phi1 f hf s y h1 h2 t ht) (fun t ht => pdb_phi2 f hf s y h1 h2 t ht)
    (pdb_phi3 f hf s y h1 h2 0 (by simp [hs, hy]))
  rw [this, pdb_iter2f, pdb_iter3f]
  simp

theorem perspective_third_differential_core (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
          (-(3 * h.1 ^ 2 * h.2 / y ^ 2) + 6 * s * h.1 * h.2 ^ 2 / y ^ 3
            - 3 * s ^ 2 * h.2 ^ 3 / y ^ 4)
        + iteratedDeriv 3 f (s / y) *
          (h.1 ^ 3 / y ^ 2 - 3 * s * h.1 ^ 2 * h.2 / y ^ 3 + 3 * s ^ 2 * h.1 * h.2 ^ 2 / y ^ 4
            - s ^ 3 * h.2 ^ 3 / y ^ 5) := by
  rw [pdb_D3 f hf s y hs hy h]
  field_simp
  ring


theorem pdb_compat_alg (κ d2 d3 s y h1 h2 : ℝ) (hκ : 0 < κ) (hs : 0 < s) (hy : 0 < y)
    (hd2 : 0 ≤ d2) (hd3 : |d3| ≤ κ * d2 / (s / y)) :
    |d3 * (h1 - s / y * h2) ^ 3 / y ^ 2 - 3 * d2 * h2 * (h1 - s / y * h2) ^ 2 / y ^ 2| ≤
      (3 + κ * Real.sqrt 2) * (d2 * (h1 - s / y * h2) ^ 2 / y) *
        Real.sqrt (h1 ^ 2 / s ^ 2 + h2 ^ 2 / y ^ 2) := by
  set a := h1 - s / y * h2 with ha
  set R := Real.sqrt (h1 ^ 2 / s ^ 2 + h2 ^ 2 / y ^ 2) with hR
  set D2 := d2 * a ^ 2 / y with hD2
  have hD2n : 0 ≤ D2 := by positivity
  have e1 : |a| / s ≤ Real.sqrt 2 * R := by
    rw [hR, ← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    have : |a| / s = |h1 / s - h2 / y| := by
      have e : a / s = h1 / s - h2 / y := by rw [ha]; field_simp
      rw [← e, abs_div, abs_of_pos hs]
    rw [this, sq_abs]
    have : h1 ^ 2 / s ^ 2 = (h1 / s) ^ 2 := by rw [div_pow]
    have h' : h2 ^ 2 / y ^ 2 = (h2 / y) ^ 2 := by rw [div_pow]
    rw [this, h']
    nlinarith [sq_nonneg (h1 / s + h2 / y)]
  have e2 : |h2| / y ≤ R := by
    rw [hR]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, sq_abs]
    have : 0 ≤ h1 ^ 2 / s ^ 2 := by positivity
    linarith
  have step1 : |d3 * a ^ 3 / y ^ 2 - 3 * d2 * h2 * a ^ 2 / y ^ 2| ≤
      |d3| * |a| ^ 3 / y ^ 2 + 3 * d2 * |h2| * a ^ 2 / y ^ 2 := by
    refine (abs_sub _ _).trans (le_of_eq ?_)
    simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hd2, abs_of_pos hy, sq_abs]
    norm_num
  have step2 : |d3| * |a| ^ 3 / y ^ 2 ≤ κ * D2 * (|a| / s) := by
    have : |d3| * |a| ^ 3 / y ^ 2 ≤ κ * d2 / (s / y) * |a| ^ 3 / y ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hd3 (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [hD2]
    have : |a| ^ 3 = |a| * a ^ 2 := by rw [← sq_abs]; ring
    rw [this]
    field_simp
  have step3 : 3 * d2 * |h2| * a ^ 2 / y ^ 2 = 3 * D2 * (|h2| / y) := by
    rw [hD2]; field_simp
  calc _ ≤ _ := step1
    _ ≤ κ * D2 * (Real.sqrt 2 * R) + 3 * D2 * R := by
      rw [step3]
      have := mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ κ * D2)
      have := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ 3 * D2)
      linarith
    _ = _ := by ring

theorem perspective_compatibility_core (f : ℝ → ℝ) (κ : ℝ)
    (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s)
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
      (3 + κ * Real.sqrt 2) * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
        Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2) := by
  rw [pdb_D3 f hf s y hs hy h, pdb_D2 f hf s y hs hy h]
  have hu : 0 < s / y := div_pos hs hy
  have H := h33 (s / y) hu
  have hd2 : 0 ≤ iteratedDeriv 2 f (s / y) := by
    have := (abs_nonneg _).trans H
    have h' : 0 ≤ κ * iteratedDeriv 2 f (s / y) := by
      by_contra hc; push_neg at hc
      have : κ * iteratedDeriv 2 f (s / y) / (s / y) < 0 := div_neg_of_neg_of_pos hc hu
      linarith
    exact (mul_nonneg_iff_of_pos_left hκ).mp h'
  exact pdb_compat_alg κ _ _ s y h.1 h.2 hκ hs hy hd2 H

theorem pdb_sc_alg (D2 D3 w r σ1 σ2 β : ℝ) (hD2 : 0 ≤ D2) (hw : 0 < w) (hβ : 0 ≤ β)
    (h36 : |D3| ≤ β * D2 * Real.sqrt (σ1 ^ 2 + σ2 ^ 2)) :
    |D3 / w - 3 * (D2 / w) * r - 2 * r ^ 3 - 2 * σ1 ^ 3 - 2 * σ2 ^ 3| ≤
      2 * (1 + β / 3) * (D2 / w + r ^ 2 + σ1 ^ 2 + σ2 ^ 2) ^ (3 / 2 : ℝ) := by
  set A := D2 / w with hA
  have hA0 : 0 ≤ A := by positivity
  set Q := A + r ^ 2 + σ1 ^ 2 + σ2 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hpow : Q ^ (3 / 2 : ℝ) = Q * Real.sqrt Q := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hQ0 (by norm_num)]; norm_num
  rw [hpow]
  set q := Real.sqrt Q with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = Q := Real.sq_sqrt hQ0
  set ρ := Real.sqrt (σ1 ^ 2 + σ2 ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρρ : ρ ^ 2 = σ1 ^ 2 + σ2 ^ 2 := Real.sq_sqrt (by positivity)
  have hρq : ρ ≤ q := by
    rw [hρ, hq]; apply Real.sqrt_le_sqrt; rw [hQ]; nlinarith [sq_nonneg r]
  -- bound 1
  have b1 : A * ρ ≤ 2 / 3 * (Q * q) := by
    have hAle : A ≤ q ^ 2 - ρ ^ 2 := by rw [hqq, hρρ, hQ]; nlinarith [sq_nonneg r]
    have : A * ρ ≤ (q ^ 2 - ρ ^ 2) * ρ := mul_le_mul_of_nonneg_right hAle hρ0
    rw [← hqq]
    nlinarith [mul_nonneg (sq_nonneg (ρ - q / 2)) (add_nonneg hρ0 hq0),
      mul_nonneg (sq_nonneg q) (sub_nonneg.2 hρq)]
  have hD3w : |D3 / w| ≤ β * A * ρ := by
    rw [abs_div, abs_of_pos hw, div_le_iff₀ hw, hA]
    have : β * (D2 / w) * ρ * w = β * D2 * ρ := by field_simp
    rw [this]; exact h36
  -- bound 2
  set p := Real.sqrt (A + r ^ 2) with hp
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hpp : p ^ 2 = A + r ^ 2 := Real.sq_sqrt (by positivity)
  have hpq : p ≤ q := by
    rw [hp, hq]; apply Real.sqrt_le_sqrt; rw [hQ]; nlinarith [sq_nonneg σ1, sq_nonneg σ2]
  have b2 : 3 * A * |r| + 2 * |r| ^ 3 ≤ 2 * p ^ 3 := by
    have hX : 0 ≤ 3 * A * |r| + 2 * |r| ^ 3 := by positivity
    have hsq : (3 * A * |r| + 2 * |r| ^ 3) ^ 2 ≤ (2 * p ^ 3) ^ 2 := by
      have e : (2 * p ^ 3) ^ 2 = 4 * (p ^ 2) ^ 3 := by ring
      rw [e, hpp, ← sq_abs r]
      have e2 : 4 * (A + |r| ^ 2) ^ 3 - (3 * A * |r| + 2 * |r| ^ 3) ^ 2 =
          4 * A ^ 3 + 3 * A ^ 2 * |r| ^ 2 := by ring
      have : 0 ≤ 4 * A ^ 3 + 3 * A ^ 2 * |r| ^ 2 := by positivity
      linarith
    exact (pow_le_pow_iff_left₀ hX (by positivity) two_ne_zero).mp hsq
  have b2' : 2 * p ^ 3 ≤ 2 * (A + r ^ 2) * q := by
    rw [← hpp]; nlinarith [mul_le_mul_of_nonneg_left hpq (sq_nonneg p)]
  have b3 : ∀ σ : ℝ, σ ^ 2 ≤ Q → 2 * |σ| ^ 3 ≤ 2 * σ ^ 2 * q := by
    intro σ hσ
    have : |σ| ≤ q := by
      rw [hq, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hσ
    have e : |σ| ^ 3 = σ ^ 2 * |σ| := by rw [← sq_abs]; ring
    rw [e]; nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg σ)]
  have b31 := b3 σ1 (by rw [hQ]; nlinarith [sq_nonneg σ2, sq_nonneg r])
  have b32 := b3 σ2 (by rw [hQ]; nlinarith [sq_nonneg σ1, sq_nonneg r])
  have tri : |D3 / w - 3 * A * r - 2 * r ^ 3 - 2 * σ1 ^ 3 - 2 * σ2 ^ 3| ≤
      |D3 / w| + 3 * A * |r| + 2 * |r| ^ 3 + 2 * |σ1| ^ 3 + 2 * |σ2| ^ 3 := by
    have h1 : |3 * A * r| = 3 * A * |r| := by rw [abs_mul, abs_mul, abs_of_nonneg hA0]; norm_num
    have h2 : ∀ x : ℝ, |2 * x ^ 3| = 2 * |x| ^ 3 := by intro x; rw [abs_mul, abs_pow]; norm_num
    calc _ ≤ |D3 / w - 3 * A * r - 2 * r ^ 3 - 2 * σ1 ^ 3| + |2 * σ2 ^ 3| := abs_sub _ _
      _ ≤ |D3 / w - 3 * A * r - 2 * r ^ 3| + |2 * σ1 ^ 3| + |2 * σ2 ^ 3| := by
          gcongr; exact abs_sub _ _
      _ ≤ |D3 / w - 3 * A * r| + |2 * r ^ 3| + |2 * σ1 ^ 3| + |2 * σ2 ^ 3| := by
          gcongr; exact abs_sub _ _
      _ ≤ |D3 / w| + |3 * A * r| + |2 * r ^ 3| + |2 * σ1 ^ 3| + |2 * σ2 ^ 3| := by
          gcongr; exact abs_sub _ _
      _ = _ := by rw [h1, h2, h2, h2]
  have hβb1 := mul_le_mul_of_nonneg_left b1 hβ
  calc _ ≤ _ := tri
    _ ≤ β * A * ρ + 2 * (A + r ^ 2) * q + 2 * σ1 ^ 2 * q + 2 * σ2 ^ 2 * q := by linarith
    _ ≤ β * (2 / 3 * (Q * q)) + 2 * (A + r ^ 2) * q + 2 * σ1 ^ 2 * q + 2 * σ2 ^ 2 * q := by
        have : β * A * ρ = β * (A * ρ) := by ring
        linarith
    _ = _ := by rw [hQ]; ring

theorem pdb_logline (φ φ1 φ2 : ℝ → ℝ) (c3 s y z h1 h2 h3 : ℝ) (V : Set ℝ) (hV : IsOpen V)
    (h0 : (0:ℝ) ∈ V)
    (hpos : ∀ t ∈ V, 0 < s + t * h1 ∧ 0 < y + t * h2 ∧ φ t < z + t * h3)
    (d1 : ∀ t ∈ V, HasDerivAt φ (φ1 t) t) (d2 : ∀ t ∈ V, HasDerivAt φ1 (φ2 t) t)
    (d3 : HasDerivAt φ2 c3 0) :
    iteratedDeriv 2 (fun t => -Real.log (z + t * h3 - φ t) - Real.log (s + t * h1)
        - Real.log (y + t * h2)) 0 =
      φ2 0 / (z - φ 0) + ((h3 - φ1 0) / (z - φ 0)) ^ 2 + (h1 / s) ^ 2 + (h2 / y) ^ 2 ∧
    iteratedDeriv 3 (fun t => -Real.log (z + t * h3 - φ t) - Real.log (s + t * h1)
        - Real.log (y + t * h2)) 0 =
      c3 / (z - φ 0) - 3 * (φ2 0 / (z - φ 0)) * ((h3 - φ1 0) / (z - φ 0))
        - 2 * ((h3 - φ1 0) / (z - φ 0)) ^ 3 - 2 * (h1 / s) ^ 3 - 2 * (h2 / y) ^ 3 := by
  have hS : ∀ t, HasDerivAt (fun t => s + t * h1) h1 t := fun t => by
    simpa using ((hasDerivAt_id t).mul_const h1).const_add s
  have hY : ∀ t, HasDerivAt (fun t => y + t * h2) h2 t := fun t => by
    simpa using ((hasDerivAt_id t).mul_const h2).const_add y
  have hW : ∀ t ∈ V, HasDerivAt (fun t => z + t * h3 - φ t) (h3 - φ1 t) t := fun t ht => by
    have hl : HasDerivAt (fun t => z + t * h3) h3 t := by
      simpa using ((hasDerivAt_id t).mul_const h3).const_add z
    exact hl.sub (d1 t ht)
  have hR : ∀ t ∈ V, HasDerivAt (fun t => h3 - φ1 t) (-φ2 t) t := fun t ht => by
    simpa using (d2 t ht).const_sub h3
  have D1 : ∀ t ∈ V, HasDerivAt (fun t => -Real.log (z + t * h3 - φ t) - Real.log (s + t * h1)
        - Real.log (y + t * h2))
      (-((h3 - φ1 t) / (z + t * h3 - φ t)) - h1 / (s + t * h1) - h2 / (y + t * h2)) t := by
    intro t ht
    obtain ⟨p1, p2, p3⟩ := hpos t ht
    exact (((hW t ht).log (by linarith)).neg.sub ((hS t).log p1.ne')).sub ((hY t).log p2.ne')
  have D2 : ∀ t ∈ V, HasDerivAt
      (fun t => -((h3 - φ1 t) / (z + t * h3 - φ t)) - h1 / (s + t * h1) - h2 / (y + t * h2))
      (φ2 t / (z + t * h3 - φ t) + ((h3 - φ1 t) / (z + t * h3 - φ t)) ^ 2
        + (h1 / (s + t * h1)) ^ 2 + (h2 / (y + t * h2)) ^ 2) t := by
    intro t ht
    obtain ⟨p1, p2, p3⟩ := hpos t ht
    have hw : z + t * h3 - φ t ≠ 0 := by linarith
    refine ((((hR t ht).div (hW t ht) hw).neg.sub ((hasDerivAt_const t h1).div (hS t) p1.ne')).sub
      ((hasDerivAt_const t h2).div (hY t) p2.ne')).congr_deriv ?_
    have := p1.ne'; have := p2.ne'
    field_simp
    ring
  have D3 : HasDerivAt
      (fun t => φ2 t / (z + t * h3 - φ t) + ((h3 - φ1 t) / (z + t * h3 - φ t)) ^ 2
        + (h1 / (s + t * h1)) ^ 2 + (h2 / (y + t * h2)) ^ 2)
      (c3 / (z - φ 0) - 3 * (φ2 0 / (z - φ 0)) * ((h3 - φ1 0) / (z - φ 0))
        - 2 * ((h3 - φ1 0) / (z - φ 0)) ^ 3 - 2 * (h1 / s) ^ 3 - 2 * (h2 / y) ^ 3) 0 := by
    obtain ⟨p1, p2, p3⟩ := hpos 0 h0
    simp only [zero_mul, add_zero] at p1 p2 p3
    have hw : z + 0 * h3 - φ 0 ≠ 0 := by simp; linarith
    have hs0 : s + 0 * h1 ≠ 0 := by simp; linarith
    have hy0 : y + 0 * h2 ≠ 0 := by simp; linarith
    refine (((d3.div (hW 0 h0) hw).add (((hR 0 h0).div (hW 0 h0) hw).pow 2)).add
      (((hasDerivAt_const 0 h1).div (hS 0) hs0).pow 2)).add
      (((hasDerivAt_const 0 h2).div (hY 0) hy0).pow 2) |>.congr_deriv ?_
    simp only [Pi.div_apply, zero_mul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have : z - φ 0 ≠ 0 := by linarith
    have := p1.ne'; have := p2.ne'
    field_simp
    ring
  constructor
  · rw [pdb_iter2 _ _ _ V hV 0 h0 D1 (D2 0 h0)]
    simp
  · exact pdb_iter3 _ _ _ _ V hV 0 h0 D1 D2 D3


theorem pdb_W_open : IsOpen {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ 0 < p.2.1} :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd))

theorem pdb_G_contDiffOn (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ × ℝ => perspective f (p.1, p.2.1))
      {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ 0 < p.2.1} :=
  (pdb_persp_contDiffOn f hf).comp (by fun_prop : ContDiff ℝ 3
    (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1))).contDiffOn (fun p hp => hp)

theorem pdb_dom_open (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) :
    IsOpen (barrierDomain f) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.2 - perspective f (p.1, p.2.1))
      {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ 0 < p.2.1} :=
    ((by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => p.2.2).continuousOn).sub
      (pdb_G_contDiffOn f hf).continuousOn
  have := hc.isOpen_inter_preimage pdb_W_open (isOpen_Ioi (a := (0:ℝ)))
  convert this using 1
  ext p
  simp [barrierDomain, and_assoc]

theorem pdb_dom_convex (f : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Ioi 0) f) :
    Convex ℝ (barrierDomain f) := by
  rintro ⟨s1, y1, z1⟩ ⟨hs1, hy1, hz1⟩ ⟨s2, y2, z2⟩ ⟨hs2, hy2, hz2⟩ a b ha hb hab
  simp only [perspective] at hz1 hz2 hs1 hs2 hy1 hy2
  have hS : 0 < a * s1 + b * s2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_nonneg hb hs2.le]
    · subst ha'; simp at hab; subst hab; simpa using hs2
  have hY : 0 < a * y1 + b * y2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_nonneg hb hy2.le]
    · subst ha'; simp at hab; subst hab; simpa using hy2
  refine ⟨by simpa using hS, by simpa using hY, ?_⟩
  simp only [perspective, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have hα : 0 ≤ a * y1 / (a * y1 + b * y2) := by positivity
  have hβ' : 0 ≤ b * y2 / (a * y1 + b * y2) := by positivity
  have hαβ : a * y1 / (a * y1 + b * y2) + b * y2 / (a * y1 + b * y2) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hY.ne']
  have hcv := hconv.2 (div_pos hs1 hy1) (div_pos hs2 hy2) hα hβ' hαβ
  have harg : (a * y1 / (a * y1 + b * y2)) • (s1 / y1) + (b * y2 / (a * y1 + b * y2)) • (s2 / y2)
      = (a * s1 + b * s2) / (a * y1 + b * y2) := by
    simp only [smul_eq_mul]; field_simp
  rw [harg] at hcv
  simp only [smul_eq_mul] at hcv
  have key : (a * y1 + b * y2) * f ((a * s1 + b * s2) / (a * y1 + b * y2)) ≤
      a * (y1 * f (s1 / y1)) + b * (y2 * f (s2 / y2)) := by
    have := mul_le_mul_of_nonneg_left hcv hY.le
    calc _ ≤ _ := this
      _ = _ := by field_simp
  have : a * (y1 * f (s1 / y1)) + b * (y2 * f (s2 / y2)) < a * z1 + b * z2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_lt_mul_of_pos_left hz1 ha'
      have := mul_le_mul_of_nonneg_left hz2.le hb
      linarith
    · subst ha'; simp at hab; subst hab; simpa using hz2
  linarith

theorem pdb_log_contDiffOn (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (logBarrier f) (barrierDomain f) := by
  have hG := (pdb_G_contDiffOn f hf).mono (fun p (hp : p ∈ barrierDomain f) => ⟨hp.1, hp.2.1⟩)
  have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ × ℝ => p.2.2 - perspective f (p.1, p.2.1))
      (barrierDomain f) :=
    ((by fun_prop : ContDiff ℝ 3 fun p : ℝ × ℝ × ℝ => p.2.2).contDiffOn).sub hG
  have h2 := (h1.log (fun p hp => (sub_pos.2 hp.2.2).ne')).neg
  have h3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ × ℝ => Real.log p.1) (barrierDomain f) :=
    ((by fun_prop : ContDiff ℝ 3 fun p : ℝ × ℝ × ℝ => p.1).contDiffOn).log
      (fun p hp => hp.1.ne')
  have h4 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ × ℝ => Real.log p.2.1) (barrierDomain f) :=
    ((by fun_prop : ContDiff ℝ 3 fun p : ℝ × ℝ × ℝ => p.2.1).contDiffOn).log
      (fun p hp => hp.2.1.ne')
  exact (h2.sub h3).sub h4

theorem pdb_f2_nonneg (f : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Ioi 0) f)
    (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (u : ℝ) (hu : 0 < u) : 0 ≤ deriv (deriv f) u := by
  have hdiff : ∀ x ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hx)
  have hmono := hconv.monotoneOn_deriv hdiff
  have := hmono.derivWithin_nonneg (x := u)
  rwa [derivWithin_of_isOpen isOpen_Ioi hu] at this


theorem den_hertog_core (f : ℝ → ℝ) (β : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hβ : 0 ≤ β)
    (h36 : ∀ s y : ℝ, 0 < s → 0 < y → ∀ h : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
        β * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
          Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2)) :
    IsSelfConcordant (1 + β / 3) (barrierDomain f) (logBarrier f) := by
  have hopen := pdb_dom_open f hf
  have hcd := pdb_log_contDiffOn f hf
  refine ⟨by positivity, hopen, pdb_dom_convex f hconv, hcd, ?_⟩
  rintro ⟨s, y, z⟩ hp ⟨h1, h2, h3⟩
  have hp' := hp
  obtain ⟨hs, hy, hz⟩ := hp'
  simp only [perspective] at hs hy hz
  rw [pdb_line _ _ hopen 3 hcd _ hp, pdb_line _ _ hopen 2 (hcd.of_le (by norm_num)) _ hp]
  have hline : (fun t : ℝ => logBarrier f ((s, y, z) + t • (h1, h2, h3))) =
      fun t => -Real.log (z + t * h3 - (y + t * h2) * f ((s + t * h1) / (y + t * h2)))
        - Real.log (s + t * h1) - Real.log (y + t * h2) := by
    funext t
    simp only [logBarrier, perspective, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [hline]
  set V : Set ℝ := {t | (s, y, z) + t • (h1, h2, h3) ∈ barrierDomain f} with hV
  have hVo : IsOpen V := hopen.preimage (by fun_prop)
  have h0 : (0:ℝ) ∈ V := by simpa [hV] using hp
  have hpos : ∀ t ∈ V, 0 < s + t * h1 ∧ 0 < y + t * h2 ∧
      (y + t * h2) * f ((s + t * h1) / (y + t * h2)) < z + t * h3 := by
    intro t ht
    simp only [hV, Set.mem_ofPred_eq, barrierDomain, perspective, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul] at ht
    exact ht
  have hposV : ∀ t ∈ V, 0 < s + t * h1 ∧ 0 < y + t * h2 := fun t ht => ⟨(hpos t ht).1, (hpos t ht).2.1⟩
  obtain ⟨e2, e3⟩ := pdb_logline _ _ (fun t => deriv (deriv f) ((s + t * h1) / (y + t * h2)) *
        (h1 - (s + t * h1) / (y + t * h2) * h2) ^ 2 / (y + t * h2)) _ s y z h1 h2 h3 V hVo h0 hpos
    (fun t ht => pdb_phi1 f hf s y h1 h2 t (hposV t ht))
    (fun t ht => pdb_phi2 f hf s y h1 h2 t (hposV t ht))
    (pdb_phi3 f hf s y h1 h2 0 (hposV 0 h0))
  rw [e2, e3]
  simp only [zero_mul, add_zero]
  have H := h36 s y hs hy (h1, h2)
  rw [pdb_D3 f hf s y hs hy, pdb_D2 f hf s y hs hy, pdb_iter2f, pdb_iter3f] at H
  simp only at H
  have hd2 : 0 ≤ deriv (deriv f) (s / y) * (h1 - s / y * h2) ^ 2 / y := by
    have := pdb_f2_nonneg f hconv hf (s / y) (div_pos hs hy)
    positivity
  have hw : 0 < z - y * f (s / y) := by linarith
  have hσ : h1 ^ 2 / s ^ 2 + h2 ^ 2 / y ^ 2 = (h1 / s) ^ 2 + (h2 / y) ^ 2 := by
    rw [div_pow, div_pow]
  rw [hσ] at H
  exact pdb_sc_alg _ _ _ _ _ _ β hd2 hw hβ H


theorem perspective_barrier_core (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s) :
    IsSelfConcordant (2 + Real.sqrt 2 / 3 * κ) (barrierDomain f) (logBarrier f) := by
  have e : (2 + Real.sqrt 2 / 3 * κ) = 1 + (3 + κ * Real.sqrt 2) / 3 := by ring
  rw [e]
  exact den_hertog_core f _ hconv hf (by positivity)
    (fun s y hs hy h => perspective_compatibility_core f κ hf hκ h33 s y hs hy h)

end PhiDivRobust.Barrier

open PhiDivRobust.Barrier


theorem solution (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s) :
    IsSelfConcordant (2 + Real.sqrt 2 / 3 * κ) (barrierDomain f) (logBarrier f) := by
  exact perspective_barrier_core f κ hconv hf hκ h33
