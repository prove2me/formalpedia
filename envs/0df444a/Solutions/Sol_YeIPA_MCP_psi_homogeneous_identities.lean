-- Prove2me | solution 1 for YeIPA.MCP.psi_homogeneous_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:38:35.61675+00:00
-- url     : https://prove2.me/submissions/1073ad79-e94c-47ce-bc96-b5033e919845

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix
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

theorem g69c_psi_homog {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ posOrthant (n + 1)) (t : ℝ) (ht : 0 < t) : psi f (t • z) = t • psi f z := by
  have hzl : z (Fin.last n) ≠ 0 := (hz _).ne'
  have hu : (fun j => Fin.init (t • z) j / (t • z) (Fin.last n)) =
      (fun j => Fin.init z j / z (Fin.last n)) := by
    funext j
    simp only [Fin.init, Pi.smul_apply, smul_eq_mul]
    field_simp
  unfold psi
  rw [hu]
  generalize f (fun j => Fin.init z j / z (Fin.last n)) = F
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.init, Finset.mul_sum]
    rw [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  · simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
    ring

theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (hf_diff : DifferentiableOn ℝ f (posOrthant n)) :
    ContinuousOn (psi f) (posOrthant (n + 1)) ∧
    (∀ z ∈ posOrthant (n + 1), ∀ t : ℝ, 0 < t → psi f (t • z) = t • psi f z) ∧
    (∀ z ∈ posOrthant (n + 1), z ⬝ᵥ psi f z = 0) ∧
    (∀ z ∈ posOrthant (n + 1), ∀ d : Fin (n + 1) → ℝ,
      z ⬝ᵥ fderiv ℝ (psi f) z d = -(psi f z ⬝ᵥ d)) :=
  ⟨g69c_psi_cont f hf_cont, fun z hz t ht => g69c_psi_homog f z hz t ht,
    fun z _ => g69c_self_dot_psi f z,
    fun z hz d => g69c_euler f z (g69c_psi_diff f hf_diff z hz) d⟩
