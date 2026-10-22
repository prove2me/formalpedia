-- Prove2me | solution 1 for YeIPA.MCP.psi_jacobian_psd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:42:32.809865+00:00
-- url     : https://prove2.me/submissions/86ae866c-2eec-46a9-9f10-a5a209fb6b20

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix Filter Topology
open YeIPA.MCP

theorem g69c_dot_psi {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (w z : Fin (n + 1) → ℝ) :
    w ⬝ᵥ psi f z = (z (Fin.last n) • Fin.init w - w (Fin.last n) • Fin.init z) ⬝ᵥ
      f (fun j => Fin.init z j / z (Fin.last n)) := by
  unfold psi
  generalize f (fun j => Fin.init z j / z (Fin.last n)) = F
  simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Fin.init, sub_mul, Finset.sum_sub_distrib]
  rw [mul_neg, Finset.mul_sum]
  have : ∀ x : Fin n, w x.castSucc * (z (Fin.last n) * F x) = z (Fin.last n) * w x.castSucc * F x :=
    fun x => by ring
  simp only [this]
  have : ∀ x : Fin n, w (Fin.last n) * (z x.castSucc * F x) = w (Fin.last n) * z x.castSucc * F x :=
    fun x => by ring
  simp only [this]
  ring

theorem g69c_self_dot_psi {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin (n + 1) → ℝ) :
    z ⬝ᵥ psi f z = 0 := by
  rw [g69c_dot_psi, sub_self, zero_dotProduct]

theorem g69c_init_pos {n : ℕ} (z : Fin (n + 1) → ℝ) (hz : z ∈ posOrthant (n + 1)) :
    (fun j => Fin.init z j / z (Fin.last n)) ∈ posOrthant n :=
  fun j => div_pos (hz _) (hz _)

theorem g69c_psi_cont {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) :
    ContinuousOn (psi f) (posOrthant (n + 1)) := by
  have hu : ContinuousOn (fun z : Fin (n + 1) → ℝ => fun j => Fin.init z j / z (Fin.last n))
      (posOrthant (n + 1)) := by
    apply continuousOn_pi.mpr
    intro j
    exact ((continuous_apply _).continuousOn).div (continuous_apply _).continuousOn
      (fun z hz => (hz _).ne')
  have hfu : ContinuousOn (fun z : Fin (n + 1) → ℝ => f (fun j => Fin.init z j / z (Fin.last n)))
      (posOrthant (n + 1)) :=
    hf_cont.comp hu (fun z hz => g69c_init_pos z hz)
  apply continuousOn_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [psi, Fin.snoc_last]
    simp only [dotProduct]
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro k _
    exact ((continuous_apply _).continuousOn).mul
      ((continuous_apply k).comp_continuousOn hfu)
  · simp only [psi, Fin.snoc_castSucc]
    exact ((continuous_apply _).continuousOn).mul ((continuous_apply k).comp_continuousOn hfu)

theorem g69c_posOrthant_open (N : ℕ) : IsOpen (posOrthant N) := by
  have : posOrthant N = ⋂ i, {x : Fin N → ℝ | 0 < x i} := by
    ext x; simp [posOrthant]
  rw [this]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))

theorem g69c_psi_diff {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_diff : DifferentiableOn ℝ f (posOrthant n)) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ posOrthant (n + 1)) : DifferentiableAt ℝ (psi f) z := by
  have hu : DifferentiableAt ℝ (fun w : Fin (n + 1) → ℝ => fun j => Fin.init w j / w (Fin.last n))
      z := by
    rw [differentiableAt_pi]
    intro j
    simp only [div_eq_mul_inv]
    exact (differentiableAt_apply (𝕜 := ℝ) (Fin.castSucc j) z).mul
      ((differentiableAt_apply (𝕜 := ℝ) (Fin.last n) z).inv (hz _).ne')
  have hf : DifferentiableAt ℝ f (fun j => Fin.init z j / z (Fin.last n)) :=
    hf_diff.differentiableAt ((g69c_posOrthant_open n).mem_nhds (g69c_init_pos z hz))
  have hfu : DifferentiableAt ℝ
      (fun w : Fin (n + 1) → ℝ => f (fun j => Fin.init w j / w (Fin.last n))) z :=
    hf.comp z hu
  rw [differentiableAt_pi]
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [psi, Fin.snoc_last]
    simp only [dotProduct]
    apply DifferentiableAt.neg
    apply DifferentiableAt.fun_sum
    intro k _
    exact (differentiableAt_apply (𝕜 := ℝ) _ z).mul (differentiableAt_pi.mp hfu k)
  · simp only [psi, Fin.snoc_castSucc]
    exact (differentiableAt_apply (𝕜 := ℝ) _ z).mul (differentiableAt_pi.mp hfu k)

theorem g69c_euler {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin (n + 1) → ℝ)
    (hpsi : DifferentiableAt ℝ (psi f) z) (d : Fin (n + 1) → ℝ) :
    z ⬝ᵥ fderiv ℝ (psi f) z d = -(psi f z ⬝ᵥ d) := by
  set L := fderiv ℝ (psi f) z
  have hγ : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have hψ : HasDerivAt (fun t : ℝ => psi f (z + t • d)) (L d) 0 := by
    have h1 : HasFDerivAt (psi f) L (z + (0 : ℝ) • d) := by
      simpa using hpsi.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hγ
  have hdot : HasDerivAt (fun t : ℝ => ∑ i, (z + t • d) i * psi f (z + t • d) i)
      (∑ i, (d i * psi f (z + (0 : ℝ) • d) i + (z + (0 : ℝ) • d) i * L d i)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hasDerivAt_pi.mp hγ i).mul (hasDerivAt_pi.mp hψ i)
  have hzero : (fun t : ℝ => ∑ i, (z + t • d) i * psi f (z + t • d) i) = fun _ => 0 := by
    funext t
    exact g69c_self_dot_psi f (z + t • d)
  rw [hzero] at hdot
  have := hdot.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simp only [zero_smul, add_zero, Finset.sum_add_distrib] at this
  unfold dotProduct
  rw [show ∑ i, psi f z i * d i = ∑ i, d i * psi f z i from
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  linarith
theorem g69c_psi_mono {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf_mono : MonotoneOnPos f) :
    MonotoneOnPos (psi f) := by
  intro z1 hz1 z2 hz2
  have e : (z1 - z2) ⬝ᵥ (psi f z1 - psi f z2) = -(z1 ⬝ᵥ psi f z2) - z2 ⬝ᵥ psi f z1 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, g69c_self_dot_psi, g69c_self_dot_psi]
    ring
  rw [e, g69c_dot_psi, g69c_dot_psi]
  set t1 := z1 (Fin.last n)
  set t2 := z2 (Fin.last n)
  have ht1 : 0 < t1 := hz1 _
  have ht2 : 0 < t2 := hz2 _
  set u1 : Fin n → ℝ := fun j => Fin.init z1 j / t1 with hu1
  set u2 : Fin n → ℝ := fun j => Fin.init z2 j / t2 with hu2
  have k1 : t2 • Fin.init z1 - z1 (Fin.last n) • Fin.init z2 = (t1 * t2) • (u1 - u2) := by
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu1, hu2]
    field_simp
    ring
  have k2 : t1 • Fin.init z2 - z2 (Fin.last n) • Fin.init z1 = -((t1 * t2) • (u1 - u2)) := by
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hu1, hu2]
    field_simp
    ring
  rw [k1, k2, neg_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hm := hf_mono u1 (g69c_init_pos z1 hz1) u2 (g69c_init_pos z2 hz2)
  rw [dotProduct_sub] at hm
  have hp : 0 < t1 * t2 := mul_pos ht1 ht2
  nlinarith

theorem g69c_hasDeriv_dot {N : ℕ} (c : Fin N → ℝ) (F : ℝ → Fin N → ℝ) (F' : Fin N → ℝ) (t : ℝ)
    (h : HasDerivAt F F' t) : HasDerivAt (fun u => c ⬝ᵥ F u) (c ⬝ᵥ F') t := by
  unfold dotProduct
  apply HasDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_pi.mp h i).const_mul (c i)

theorem g69c_f_mono {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (hf_psd : ∀ x ∈ posOrthant n, ∀ d : Fin n → ℝ, 0 ≤ d ⬝ᵥ fderiv ℝ f x d) :
    MonotoneOnPos f := by
  intro x1 hx1 x2 hx2
  set v := x1 - x2
  set γ : ℝ → Fin n → ℝ := fun t => x2 + t • v
  have hγmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ posOrthant n := by
    intro t ht i
    simp only [γ, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h1 := hx1 i; have h2 := hx2 i
    rcases lt_or_eq_of_le ht.2 with h | h
    · nlinarith [mul_nonneg ht.1 h1.le, mul_pos (sub_pos.2 h) h2]
    · subst h; linarith
  have hγd : ∀ t, HasDerivAt γ v t := by
    intro t
    have h := ((hasDerivAt_id t).smul_const v).const_add x2
    rw [one_smul] at h
    exact h
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun u => v ⬝ᵥ f (γ u)) (v ⬝ᵥ fderiv ℝ f (γ t) v) t := by
    intro t ht
    have hfd : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) :=
      (hf_diff.differentiableAt ((g69c_posOrthant_open n).mem_nhds (hγmem t ht))).hasFDerivAt
    exact g69c_hasDeriv_dot v _ _ t (hfd.comp_hasDerivAt t (hγd t))
  have hmono : MonotoneOn (fun u => v ⬝ᵥ f (γ u)) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt) ?_
    intro t ht
    exact hf_psd _ (hγmem t (interior_subset ht)) v
  have := hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [γ, zero_smul, add_zero, one_smul, v, add_sub_cancel] at this
  rw [dotProduct_sub]
  linarith

theorem g69c_psd_of_mono {N : ℕ} (g : (Fin N → ℝ) → (Fin N → ℝ)) (hg : MonotoneOnPos g)
    (z : Fin N → ℝ) (hz : z ∈ posOrthant N) (hd : DifferentiableAt ℝ g z) (d : Fin N → ℝ) :
    0 ≤ d ⬝ᵥ fderiv ℝ g z d := by
  set L := fderiv ℝ g z
  have hγ : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have hψ : HasDerivAt (fun t : ℝ => g (z + t • d)) (L d) 0 := by
    have h1 : HasFDerivAt g L (z + (0 : ℝ) • d) := by simpa using hd.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hγ
  have hφ := g69c_hasDeriv_dot d _ _ 0 hψ
  rw [hasDerivAt_iff_tendsto_slope_zero] at hφ
  have hφ' : Tendsto (fun t : ℝ => t⁻¹ • (d ⬝ᵥ g (z + (0 + t) • d) - d ⬝ᵥ g (z + (0:ℝ) • d)))
      (𝓝[>] 0) (𝓝 (d ⬝ᵥ L d)) :=
    hφ.mono_left (nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
  apply ge_of_tendsto hφ'
  have hcont : Tendsto (fun t : ℝ => z + t • d) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous (fun t : ℝ => z + t • d) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), z + t • d ∈ posOrthant N :=
    hcont.eventually ((g69c_posOrthant_open N).mem_nhds hz)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  have hm := hg (z + t • d) ht z hz
  rw [add_sub_cancel_left, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hm
  have htp : (0 : ℝ) < t := htpos
  have : 0 ≤ d ⬝ᵥ g (z + t • d) - d ⬝ᵥ g z := by
    by_contra hc
    push Not at hc
    nlinarith
  positivity

theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (hf_psd : ∀ x ∈ posOrthant n, ∀ d : Fin n → ℝ, 0 ≤ d ⬝ᵥ fderiv ℝ f x d) :
    ∀ z ∈ posOrthant (n + 1), ∀ d : Fin (n + 1) → ℝ, 0 ≤ d ⬝ᵥ fderiv ℝ (psi f) z d := by
  intro z hz d
  exact g69c_psd_of_mono (psi f) (g69c_psi_mono f (g69c_f_mono f hf_diff hf_psd)) z hz
    (g69c_psi_diff f hf_diff z hz) d
