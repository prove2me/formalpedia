-- Prove2me | solution 1 for PhiDivRobust.Barrier.perspective_third_differential
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:57:28.378921+00:00
-- url     : https://prove2.me/submissions/46088186-e824-4270-9e40-9860e27281b9

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

end PhiDivRobust.Barrier

open PhiDivRobust.Barrier


theorem solution (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
          (-(3 * h.1 ^ 2 * h.2 / y ^ 2) + 6 * s * h.1 * h.2 ^ 2 / y ^ 3
            - 3 * s ^ 2 * h.2 ^ 3 / y ^ 4)
        + iteratedDeriv 3 f (s / y) *
          (h.1 ^ 3 / y ^ 2 - 3 * s * h.1 ^ 2 * h.2 / y ^ 3 + 3 * s ^ 2 * h.1 * h.2 ^ 2 / y ^ 4
            - s ^ 3 * h.2 ^ 3 / y ^ 5) := by
  exact perspective_third_differential_core f hf s y hs hy h
