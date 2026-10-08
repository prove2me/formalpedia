-- Prove2me | solution 1 for PhiDivRobust.Barrier.perspective_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:59:13.793191+00:00
-- url     : https://prove2.me/submissions/4a2697dd-a06d-44c7-98df-990788c45f43

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective



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

end PhiDivRobust.Barrier

open PhiDivRobust.Barrier


theorem solution (f : ℝ → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioi 0) f) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0)) (hκ : 0 < κ)
    (h33 : ∀ s : ℝ, 0 < s → |iteratedDeriv 3 f s| ≤ κ * iteratedDeriv 2 f s / s)
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    |iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h)| ≤
      (3 + κ * Real.sqrt 2) * iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) *
        Real.sqrt (h.1 ^ 2 / s ^ 2 + h.2 ^ 2 / y ^ 2) := by
  exact perspective_compatibility_core f κ hf hκ h33 s y hs hy h
