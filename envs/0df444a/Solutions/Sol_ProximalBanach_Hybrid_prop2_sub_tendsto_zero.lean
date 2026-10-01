-- Prove2me | solution 1 for ProximalBanach.Hybrid.prop2_sub_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:17:35.821376+00:00
-- url     : https://prove2.me/submissions/5c940d75-7581-476d-884a-857f7bf4c763

import Definitions.Def_ProximalBanach_Hybrid_Basic
set_option maxHeartbeats 3000000
open Filter Topology Set
namespace ProximalBanach.Hybrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem dual_norm (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (x : E) : ‖J x‖ = ‖x‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hJ x).2

private theorem phi_norm_gap (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (y z : E) : (‖y‖ - ‖z‖)^2 ≤ phi J y z := by
  have heval : J z y ≤ ‖z‖ * ‖y‖ :=
    (le_abs_self _).trans (by simpa [dual_norm J hJ z] using (J z).le_opNorm y)
  unfold phi
  nlinarith

 theorem phi_controls_distance [UniformConvexSpace E]
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (M eps : ℝ) (hM : 0 ≤ M) (heps : 0 < eps) :
    ∃ rho > 0, ∀ y z : E, ‖y‖ ≤ M → ‖z‖ ≤ M → phi J y z < rho → ‖y-z‖ < eps := by
  have hMp : 0 < M+1 := by linarith
  obtain ⟨δ0,hδ0,hmod⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos heps hMp)
  let δ := min δ0 1
  have hδ : 0 < δ := lt_min hδ0 zero_lt_one
  let eta := min (eps/4) (δ*eps^2/(128*(M+1)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  let rho := min (eta^2) (δ*eps^2/16)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  refine ⟨rho,hrho,?_⟩
  intro y z hy hz hphi
  by_contra hclose
  have hsep : eps ≤ ‖y-z‖ := le_of_not_gt hclose
  let a := ‖y‖
  let b := ‖z‖
  let m := max a b
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have haM : a ≤ M := hy
  have hbM : b ≤ M := hz
  have ham : a ≤ m := le_max_left _ _
  have hbm : b ≤ m := le_max_right _ _
  have hmM : m ≤ M := max_le hy hz
  have hgap : (a-b)^2 < eta^2 :=
    (phi_norm_gap J hJ y z).trans_lt (hphi.trans_le (min_le_left _ _))
  have hab1 : -eta < a-b := by nlinarith [sq_nonneg (a-b+eta)]
  have hab2 : a-b < eta := by nlinarith [sq_nonneg (a-b-eta)]
  have hmet : m ≤ b+eta := max_le (by linarith) (by linarith)
  have hsub : ‖y-z‖ ≤ a+b := norm_sub_le y z
  have hmpos : 0 < m := by linarith
  have heta1 : eta ≤ eps/4 := min_le_left _ _
  have hblow : eps/4 ≤ b := by linarith
  have hmlow : eps/4 ≤ m := hblow.trans hbm
  have hyn : ‖m⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos]
    exact (inv_mul_le_one₀ hmpos).mpr ham
  have hzn : ‖m⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos]
    exact (inv_mul_le_one₀ hmpos).mpr hbm
  have hdist : eps/(M+1) ≤ ‖m⁻¹ • y - m⁻¹ • z‖ := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos,← div_eq_inv_mul]
    apply (div_le_div_iff₀ hMp hmpos).mpr
    nlinarith
  have hadd := hmod hyn hzn hdist
  rw [← smul_add,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hmpos,← div_eq_inv_mul] at hadd
  have hsum : ‖y+z‖ ≤ (2-δ)*m := by
    have hh := (div_le_iff₀ hmpos).mp hadd
    have hδle : δ ≤ δ0 := min_le_left _ _
    nlinarith
  have heval : J z y + b^2 ≤ b*‖y+z‖ := by
    have h1 := (le_abs_self (J z (y+z))).trans ((J z).le_opNorm (y+z))
    simpa only [map_add,(hJ z).1,dual_norm J hJ z] using h1
  have hpair : J z y + b^2 ≤ b*((2-δ)*m) :=
    heval.trans (mul_le_mul_of_nonneg_left hsum hb)
  have hphi_lower : a^2+3*b^2-4*b*m+2*δ*b*m ≤ phi J y z := by
    dsimp [phi,a,b]
    dsimp [a,b] at hpair
    nlinarith
  have hbmup : b*m ≤ b*(b+eta) := mul_le_mul_of_nonneg_left hmet hb
  have habup : 0 ≤ b*(a-b+eta) := mul_nonneg hb (by linarith)
  have hbEta : b*eta ≤ M*eta := mul_le_mul_of_nonneg_right hbM heta.le
  have hbase : -6*M*eta ≤ a^2+3*b^2-4*b*m := by nlinarith [sq_nonneg (a-b)]
  have hbmlo : eps^2/16 ≤ b*m := by
    have hh := mul_le_mul hblow hmlow (by positivity : 0 ≤ eps/4) hb
    nlinarith
  have hbig := mul_le_mul_of_nonneg_left hbmlo (show 0 ≤ 2*δ by positivity)
  have hetascale : 128*(M+1)*eta ≤ δ*eps^2 :=
    by
    have hh : eta * (128*(M+1)) ≤ δ*eps^2 :=
      (le_div_iff₀ (show 0 < 128*(M+1) by positivity)).mp (min_le_right _ _)
    nlinarith
  have hsmall : 6*M*eta ≤ δ*eps^2/16 := by nlinarith [mul_nonneg hM heta.le]
  have hrhobd : rho ≤ δ*eps^2/16 := min_le_right _ _
  nlinarith

theorem phi_sub_tendsto_zero [UniformConvexSpace E]
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (y z : ℕ → E) (hφ : Tendsto (fun n => phi J (y n) (z n)) atTop (𝓝 0))
    (hb : Bornology.IsBounded (Set.range y) ∨ Bornology.IsBounded (Set.range z)) :
    Tendsto (fun n => y n-z n) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop, phi J (y n) (z n) < 1 :=
    hφ.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hgap : ∀ᶠ n in atTop, |‖y n‖-‖z n‖| < 1 := by
    filter_upwards [hsmall] with n hn
    have hg := (phi_norm_gap J hJ (y n) (z n)).trans_lt hn
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (‖y n‖-‖z n‖+1),sq_nonneg (‖y n‖-‖z n‖-1)]
  obtain ⟨M,hM,hbd⟩ : ∃ M:ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ‖y n‖ ≤ M ∧ ‖z n‖ ≤ M := by
    rcases hb with hy | hz
    · obtain ⟨B,hB⟩ := hy.exists_norm_le
      refine ⟨max B 0+1,by positivity,?_⟩
      filter_upwards [hgap] with n hn
      have hbn := hB (y n) (Set.mem_range_self n)
      have hmax := le_max_left B 0
      obtain ⟨hlo,hhi⟩ := abs_lt.mp hn
      constructor <;> linarith
    · obtain ⟨B,hB⟩ := hz.exists_norm_le
      refine ⟨max B 0+1,by positivity,?_⟩
      filter_upwards [hgap] with n hn
      have hbn := hB (z n) (Set.mem_range_self n)
      have hmax := le_max_left B 0
      obtain ⟨hlo,hhi⟩ := abs_lt.mp hn
      constructor <;> linarith
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨rho,hrho,hcontrol⟩ := phi_controls_distance J hJ M eps hM heps
  have hnear := hφ.eventually (gt_mem_nhds hrho)
  filter_upwards [hbd,hnear] with n hn hp
  simpa only [dist_zero_right] using hcontrol (y n) (z n) hn.1 hn.2 hp
end ProximalBanach.Hybrid

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 2 (p. 940): in a uniformly convex smooth Banach space, if
`φ(y_n, z_n) → 0` and either `{y_n}` or `{z_n}` is bounded, then `y_n - z_n → 0`. -/
theorem _root_.solution [UniformConvexSpace E] (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (y z : ℕ → E)
    (hφ : Tendsto (fun n => phi J (y n) (z n)) atTop (𝓝 0))
    (hb : Bornology.IsBounded (Set.range y) ∨ Bornology.IsBounded (Set.range z)) :
    Tendsto (fun n => y n - z n) atTop (𝓝 0) := by
  exact phi_sub_tendsto_zero J hJ y z hφ hb

end ProximalBanach.Hybrid
