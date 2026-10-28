-- Prove2me | solution 1 for ReinfRegGames.StrictStable.theorem_5_2_iv
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T05:45:01.010835+00:00
-- url     : https://prove2.me/submissions/4b4509d6-5d33-464e-b1eb-8460f55a91ee

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model
import Definitions.Def_ReinfRegGames_StrictStable_Stability


section
open Finset Matrix ReinfRegGames.Extinction
namespace StabilityProof
open scoped BigOperators
variable {B : Type*} [Fintype B]

lemma dot_simplex_abs (y x : B → ℝ) (hx : x ∈ stdSimplex ℝ B) :
    |y ⬝ᵥ x| ≤ ‖y‖ := by
  calc
    |y ⬝ᵥ x| ≤ ∑ i, |y i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖y‖ * x i := Finset.sum_le_sum fun i _ => by
      rw [abs_mul, abs_of_nonneg (hx.1 i)]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i) (hx.1 i)
    _ = ‖y‖ := by rw [← Finset.mul_sum, hx.2, mul_one]

lemma choice_exists {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p : B → ℝ} (hp : p ∈ stdSimplex ℝ B) (y : B → ℝ) :
    ∃ x, IsChoice h y x := by
  obtain ⟨x, hx, hm⟩ := (isCompact_stdSimplex ℝ B).exists_isMaxOn ⟨p, hp⟩
    ((by fun_prop : Continuous (fun x : B → ℝ => y ⬝ᵥ x)).continuousOn.sub hh.1)
  exact ⟨x, hx, fun z hz => hm hz⟩

lemma conj_eq_choice {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {y x : B → ℝ} (hx : IsChoice h y x) : conj h y = y ⬝ᵥ x - h x := by
  have hb : BddAbove ((fun z => y ⬝ᵥ z - h z) '' stdSimplex ℝ B) :=
    (isCompact_stdSimplex ℝ B).bddAbove_image
      ((by fun_prop : Continuous (fun z : B → ℝ => y ⬝ᵥ z)).continuousOn.sub hh.1)
  exact le_antisymm (csSup_le ⟨_, ⟨x, hx.1, rfl⟩⟩ (by rintro _ ⟨z,hz,rfl⟩; exact hx.2 z hz))
    (le_csSup hb ⟨x,hx.1,rfl⟩)

lemma coupling_eq_choice {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p y x : B → ℝ} (hx : IsChoice h y x) :
    fenchelCoupling h p y = h p + y ⬝ᵥ x - h x - y ⬝ᵥ p := by
  rw [fenchelCoupling, conj_eq_choice hh hx]; ring

lemma coupling_nonneg {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p y x : B → ℝ} (hp : p ∈ stdSimplex ℝ B) (hx : IsChoice h y x) :
    0 ≤ fenchelCoupling h p y := by
  rw [coupling_eq_choice hh hx]; linarith [hx.2 p hp]

lemma penalty_bounded {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x ∈ stdSimplex ℝ B, |h x| ≤ H := by
  obtain ⟨H,hH⟩ := (isCompact_stdSimplex ℝ B).bddAbove_image hh.1.norm
  refine ⟨max 0 H, le_max_left _ _, fun x hx => ?_⟩
  have hb : |h x| ≤ H := by simpa only [Real.norm_eq_abs] using hH ⟨x,hx,rfl⟩
  exact hb.trans (le_max_right _ _)

lemma conj_sub_le {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p : B → ℝ} (hp : p ∈ stdSimplex ℝ B) (y z : B → ℝ) :
    conj h y - conj h z ≤ ‖y-z‖ := by
  obtain ⟨x,hx⟩ := choice_exists hh hp y
  obtain ⟨w,hw⟩ := choice_exists hh hp z
  rw [conj_eq_choice hh hx, conj_eq_choice hh hw]
  have ho := hw.2 x hx.1
  have hd := (le_abs_self ((y-z) ⬝ᵥ x)).trans (dot_simplex_abs (y-z) x hx.1)
  rw [sub_dotProduct] at hd
  linarith

lemma conj_continuous {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p : B → ℝ} (hp : p ∈ stdSimplex ℝ B) : Continuous (conj h) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have hz := conj_sub_le hh hp z y
    rw [norm_sub_rev] at hz
    linarith
  · exact conj_sub_le hh hp y z

lemma coupling_continuous {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p : B → ℝ} (hp : p ∈ stdSimplex ℝ B) : Continuous (fenchelCoupling h p) := by
  unfold fenchelCoupling
  exact (continuous_const.add (conj_continuous hh hp)).sub (by fun_prop)
end StabilityProof
end

section
open Finset Matrix ReinfRegGames.Extinction
namespace StabilityProof
variable {B : Type*} [Fintype B]

lemma sqDist_nonneg (p x : B → ℝ) : 0 ≤ sqDist p x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma sqDist_symm (p x : B → ℝ) : sqDist p x = sqDist x p := by
  unfold sqDist; apply Finset.sum_congr rfl; intro i _; ring

lemma fenchel_lower_bound {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {p y x : B → ℝ} (hp : p ∈ stdSimplex ℝ B) (hx : IsChoice h y x) :
    K / 2 * sqDist p x ≤ fenchelCoupling h p y := by
  have hf := coupling_nonneg hh hp hx
  by_contra hn
  have hlt : fenchelCoupling h p y < K / 2 * sqDist p x := lt_of_not_ge hn
  let L := K / 2 * sqDist p x
  have hL : 0 < L := lt_of_le_of_lt hf hlt
  let t := (L - fenchelCoupling h p y) / (2*L)
  have ht : 0 < t := div_pos (sub_pos.mpr hlt) (by positivity)
  have ht1 : t ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2*L)).mpr (by linarith)
  have hid : t*(2*L) = L - fenchelCoupling h p y := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 2*L))
  have hs := hh.2.2.2 p hp x hx.1 t ⟨ht.le,ht1⟩
  have hm := hx.2 (t • p + (1-t) • x)
    ((convex_stdSimplex ℝ B) hp hx.1 ht.le (by linarith) (by ring))
  have hd : y ⬝ᵥ (t • p + (1-t) • x) = t*(y ⬝ᵥ p)+(1-t)*(y ⬝ᵥ x) := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hd] at hm
  have hcouple := coupling_eq_choice hh hx (p:=p)
  have hineq : t * ((1-t)*L - fenchelCoupling h p y) ≤ 0 := by dsimp [L]; nlinarith
  have hhineq : (1-t)*L - fenchelCoupling h p y ≤ 0 := by
    by_contra hbad
    exact (not_lt_of_ge hineq) (mul_pos ht (lt_of_not_ge hbad))
  nlinarith

lemma norm_sub_sq_le_sqDist (p x : B → ℝ) : ‖p-x‖^2 ≤ sqDist p x := by
  have hn : ‖p-x‖ ≤ Real.sqrt (sqDist p x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (sqDist_nonneg p x)).mpr
    have hi : (p i-x i)^2 ≤ sqDist p x := Finset.single_le_sum (fun j _ => sq_nonneg (p j-x j)) (Finset.mem_univ i)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using hi
  nlinarith [Real.sq_sqrt (sqDist_nonneg p x), norm_nonneg (p-x), Real.sqrt_nonneg (sqDist p x)]

lemma choice_norm_sq_bound {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {y z x w : B → ℝ} (hx : IsChoice h y x) (hw : IsChoice h z w) :
    K * ‖x-w‖^2 ≤ 2*‖y-z‖ := by
  have h1 := fenchel_lower_bound hh hw.1 hx
  have h2 := fenchel_lower_bound hh hx.1 hw
  rw [coupling_eq_choice hh hx, sqDist_symm w x] at h1
  rw [coupling_eq_choice hh hw] at h2
  have hd1 := dot_simplex_abs (y-z) x hx.1
  have hd2 := dot_simplex_abs (y-z) w hw.1
  rw [sub_dotProduct] at hd1 hd2
  have ha1 := (abs_le.mp hd1).2
  have ha2 := (abs_le.mp hd2).1
  have hn := mul_le_mul_of_nonneg_left (norm_sub_sq_le_sqDist x w) hh.2.2.1.le
  nlinarith

lemma choice_continuousOn {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {T : Type*} [TopologicalSpace T] {s : Set T} {y x : T → B → ℝ}
    (hy : ContinuousOn y s) (hx : ∀ t ∈ s, IsChoice h (y t) (x t)) : ContinuousOn x s := by
  intro t ht
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  have hK : 0 < K := hh.2.2.1
  have hδ : 0 < K*ε^2/2 := by positivity
  have he := (Metric.continuousWithinAt_iff'.mp (hy t ht)) (K*ε^2/2) hδ
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzs
  rw [dist_eq_norm] at hz ⊢
  have hb := choice_norm_sq_bound hh (hx z hzs) (hx t ht)
  have hn := norm_nonneg (x z-x t)
  have hs : ‖x z-x t‖^2 < ε^2 := (mul_lt_mul_iff_right₀ hK).mp (hb.trans_lt (by linarith))
  nlinarith
end StabilityProof
end

section
open Finset Matrix ReinfRegGames.Extinction
namespace StabilityProof
variable {B : Type*} [Fintype B] [DecidableEq B]

lemma vertex_reflect_simplex {a : B} {x : B → ℝ} (hx : x ∈ stdSimplex ℝ B)
    (ha : 1/2 ≤ x a) : (2:ℝ) • x - Pi.single a 1 ∈ stdSimplex ℝ B := by
  constructor
  · intro i
    by_cases hi : i=a
    · subst i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]; linarith
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hi, sub_zero]
      exact mul_nonneg (by norm_num) (hx.1 i)
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    norm_num [hx.2]

lemma vertex_coupling_upper {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {a : B} {y x : B → ℝ} (hx : IsChoice h y x) (ha : 1/2 ≤ x a) :
    fenchelCoupling h (Pi.single a 1) y ≤
      h (Pi.single a 1) + h ((2:ℝ) • x - Pi.single a 1) - 2*h x := by
  have hm := hx.2 _ (vertex_reflect_simplex hx.1 ha)
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hm
  rw [coupling_eq_choice hh hx]
  linarith

lemma vertex_small_coupling {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    (a : B) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y x : B → ℝ, IsChoice h y x → dist x (Pi.single a 1) < δ →
      fenchelCoupling h (Pi.single a 1) y < ε := by
  let p : B → ℝ := Pi.single a 1
  have hp : p ∈ stdSimplex ℝ B := single_mem_stdSimplex ℝ a
  obtain ⟨η,hη,hcont⟩ := Metric.continuousWithinAt_iff.mp (hh.1 p hp) (ε/3) (by positivity)
  refine ⟨min (1/4) (η/3), lt_min (by norm_num) (by positivity), fun y x hx hd => ?_⟩
  have hd1 : dist x p < 1/4 := lt_of_lt_of_le hd (min_le_left _ _)
  have hdη : dist x p < η/3 := lt_of_lt_of_le hd (min_le_right _ _)
  have ha : 1/2 ≤ x a := by
    have hi := norm_le_pi_norm (x-p) a
    have hpval : p a=1 := by simp [p]
    simp only [Pi.sub_apply, hpval, Real.norm_eq_abs] at hi
    rw [dist_eq_norm] at hd1
    have hi' := (abs_le.mp hi).1
    linarith
  let z : B → ℝ := (2:ℝ) • x-p
  have hz : z ∈ stdSimplex ℝ B := vertex_reflect_simplex hx.1 ha
  have hid : z-p = (2:ℝ) • (x-p) := by ext i; simp [z]; ring
  have hdz : dist z p < η := by
    rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [dist_eq_norm] at hdη
    linarith
  have hc1 := hcont hx.1 (show dist x p < η by linarith)
  have hc2 := hcont hz hdz
  rw [Real.dist_eq] at hc1 hc2
  have hu := vertex_coupling_upper hh hx ha
  change fenchelCoupling h p y ≤ h p + h z - 2*h x at hu
  have hl1 := (abs_lt.mp hc1).1
  have hl2 := (abs_lt.mp hc2).2
  linarith
end StabilityProof
end

section
open Finset Matrix ReinfRegGames.Extinction
namespace StabilityProof
variable {B : Type*} [Fintype B] [DecidableEq B]
lemma relative_objective (a : B) (y x : B → ℝ) (hx : x ∈ stdSimplex ℝ B) :
    y ⬝ᵥ x - y ⬝ᵥ (Pi.single a 1) = ∑ i, x i*(y i-y a) := by
  simp only [dotProduct_single, mul_one, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx.2, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma vertex_coupling_mono {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    (a : B) {y z x w : B → ℝ} (hx : IsChoice h y x) (hw : IsChoice h z w)
    (hrel : ∀ i, z i-z a ≤ y i-y a) :
    fenchelCoupling h (Pi.single a 1) z ≤ fenchelCoupling h (Pi.single a 1) y := by
  have hs : z ⬝ᵥ w-z ⬝ᵥ (Pi.single a 1) ≤ y ⬝ᵥ w-y ⬝ᵥ (Pi.single a 1) := by
    rw [relative_objective a z w hw.1, relative_objective a y w hw.1]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrel i) (hw.1.1 i)
  have hm := hx.2 w hw.1
  rw [coupling_eq_choice hh hw, coupling_eq_choice hh hx]
  linarith
end StabilityProof
end

section
open Finset ReinfRegGames.Extinction ReinfRegGames.StrictStable
namespace StabilityProof
open scoped BigOperators Classical
lemma lottery_simplex {B : Type*} [Fintype B] (x : B → ℝ) :
    AGT.IsLottery x ↔ x ∈ stdSimplex ℝ B := Iff.rfl
lemma expected_update {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (x : ∀ k, A k → ℝ) (k : ι) (τ : A k → ℝ) :
    AGT.expectedPayoff u (Function.update x k τ) k =
      ∑ s : ∀ j, A j, τ (s k) * (∏ j ∈ Finset.univ.erase k, x j (s j)) * u k s := by
  unfold AGT.expectedPayoff AGT.profileProb
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  simp only [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase k, Function.update x k τ j (s j)) =
      ∏ j ∈ Finset.univ.erase k, x j (s j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  ring
lemma expected_mixture {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (x : ∀ k, A k → ℝ) (k : ι) (τ : A k → ℝ) :
    AGT.expectedPayoff u (Function.update x k τ) k = ∑ a, τ a * payoffVec u x k a := by
  rw [expected_update]
  simp only [payoffVec, expected_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [Pi.single_apply, mul_ite, ite_mul, mul_assoc]
lemma expected_self_mixture {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (x : ∀ k, A k → ℝ) (k : ι) :
    AGT.expectedPayoff u x k = ∑ a, x k a * payoffVec u x k a := by
  simpa using expected_mixture u x k (x k)
lemma strict_nash_pure {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (x : ∀ k, A k → ℝ) (hx : IsStrictNash u x) :
    ∀ k, ∃ a : A k, x k = Pi.single a 1 ∧
      ∀ b : A k, b ≠ a → payoffVec u x k b < payoffVec u x k a := by
  intro k
  have hlot := hx.1 k
  have ha : ∃ a : A k, 0 < x k a := by
    by_contra hh
    push Not at hh
    have hz : ∑ a, x k a ≤ 0 := Finset.sum_nonpos (fun a _ => hh a)
    linarith [hlot.2]
  have hp : ∃ a : A k, x k = Pi.single a 1 := by
    by_contra hh
    push Not at hh
    have hd : ∀ a : A k, payoffVec u x k a < AGT.expectedPayoff u x k := by
      intro a
      apply hx.2 k (Pi.single a 1)
      · constructor
        · intro b; simp only [Pi.single_apply]; split_ifs <;> norm_num
        · simp
      · exact (hh a).symm
    have hsum : ∑ a, x k a * payoffVec u x k a < ∑ a, x k a * AGT.expectedPayoff u x k := by
      apply Finset.sum_lt_sum
      · intro a _
        exact mul_le_mul_of_nonneg_left (hd a).le (hlot.1 a)
      · obtain ⟨a,ha⟩ := ha
        exact ⟨a,Finset.mem_univ a,mul_lt_mul_of_pos_left (hd a) ha⟩
    rw [← expected_self_mixture, ← Finset.sum_mul, hlot.2, one_mul] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨a,ha⟩ := hp
  refine ⟨a,ha,?_⟩
  intro b hb
  have hd : payoffVec u x k b < AGT.expectedPayoff u x k := by
    apply hx.2 k (Pi.single b 1)
    · constructor
      · intro c; simp only [Pi.single_apply]; split_ifs <;> norm_num
      · simp
    · rw [ha]
      intro he
      have := congrFun he b
      simp [hb] at this
  have he : AGT.expectedPayoff u x k = payoffVec u x k a := by
    rw [expected_self_mixture u x k, ha]
    simp [Pi.single_apply]
  exact he ▸ hd
end StabilityProof
end

section
open Finset Set ReinfRegGames.Extinction ReinfRegGames.StrictStable
namespace StabilityProof
open scoped BigOperators Classical
lemma payoff_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k,A k) → ℝ) (k : ι) (a : A k) :
    Continuous (fun x : ∀ k,A k → ℝ => payoffVec u x k a) := by
  simp only [payoffVec, expected_update]
  fun_prop
lemma local_gap {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k,A k) → ℝ) (p : ∀ k,A k → ℝ)
    (k : ι) (a b : A k) (hgap : payoffVec u p k b < payoffVec u p k a) :
    ∃ δ > 0, ∃ γ > 0, ∀ x : ∀ k,A k → ℝ, dist x p < δ →
      payoffVec u x k b - payoffVec u x k a ≤ -γ := by
  let γ := (payoffVec u p k a - payoffVec u p k b)/2
  have hg : 0 < γ := by dsimp [γ]; linarith
  have hc : ContinuousAt (fun x => payoffVec u x k b - payoffVec u x k a) p :=
    ((payoff_continuous u k b).sub (payoff_continuous u k a)).continuousAt
  obtain ⟨δ,hδ,hball⟩ := Metric.continuousAt_iff.mp hc γ hg
  refine ⟨δ,hδ,γ,hg,?_⟩
  intro x hx
  have hh := hball hx
  rw [Real.dist_eq] at hh
  have := (abs_lt.mp hh).2
  dsimp [γ] at *
  linarith
lemma finite_positive_lower {I : Type*} [Fintype I] (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  have aux : ∀ s : Finset I, ∃ δ > 0, ∀ i ∈ s, δ ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ,hδ,hbound⟩ := ih
      refine ⟨min (f a) δ, lt_min (hf a) hδ, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound i hi)
  obtain ⟨δ,hδ,hh⟩ := aux Finset.univ
  exact ⟨δ,hδ,fun i => hh i (Finset.mem_univ i)⟩
lemma uniform_payoff_gap {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k,A k) → ℝ) (p : ∀ k,A k → ℝ) (a : ∀ k,A k)
    (hg : ∀ k b, b ≠ a k → payoffVec u p k b < payoffVec u p k (a k)) :
    ∃ δ > 0, ∃ γ > 0, ∀ x : ∀ k,A k → ℝ, dist x p < δ →
      ∀ k b, b ≠ a k → payoffVec u x k b - payoffVec u x k (a k) ≤ -γ := by
  let I := Σ k, {b : A k // b ≠ a k}
  have hlocal : ∀ i : I, ∃ δ > 0, ∃ γ > 0, ∀ x : ∀ k,A k → ℝ,
      dist x p < δ → payoffVec u x i.1 i.2.1 - payoffVec u x i.1 (a i.1) ≤ -γ := by
    intro i
    exact local_gap u p i.1 (a i.1) i.2.1 (hg i.1 i.2.1 i.2.2)
  choose δ hδ γ hγ hh using hlocal
  obtain ⟨D,hD,hDb⟩ := finite_positive_lower δ hδ
  obtain ⟨G,hG,hGb⟩ := finite_positive_lower γ hγ
  refine ⟨D,hD,G,hG,?_⟩
  intro x hx k b hb
  have hv := hh (⟨k,⟨b,hb⟩⟩ : I) x (hx.trans_le (hDb _))
  exact hv.trans (neg_le_neg (hGb _))
end StabilityProof
end

section
open Finset ReinfRegGames.Extinction
namespace StabilityProof
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ k, Fintype (A k)]

noncomputable def totalCoupling (h : ∀ k, (A k → ℝ) → ℝ) (p y : ∀ k,A k → ℝ) : ℝ :=
  ∑ k, fenchelCoupling (h k) (p k) (y k)

lemma totalCoupling_continuous {h : ∀ k, (A k → ℝ) → ℝ} {K : ι → ℝ}
    (hh : ∀ k, IsPenalty (h k) (K k)) {p : ∀ k,A k → ℝ}
    (hp : ∀ k, p k ∈ stdSimplex ℝ (A k)) : Continuous (totalCoupling h p) := by
  apply continuous_finsetSum
  intro k _
  exact (coupling_continuous (hh k) (hp k)).comp (continuous_apply k)

lemma totalCoupling_nonneg {h : ∀ k, (A k → ℝ) → ℝ} {K : ι → ℝ}
    (hh : ∀ k, IsPenalty (h k) (K k)) {p y x : ∀ k,A k → ℝ}
    (hp : ∀ k, p k ∈ stdSimplex ℝ (A k)) (hx : ∀ k, IsChoice (h k) (y k) (x k)) :
    0 ≤ totalCoupling h p y := Finset.sum_nonneg fun k _ => coupling_nonneg (hh k) (hp k) (hx k)

lemma total_small_dist {h : ∀ k, (A k → ℝ) → ℝ} {K : ι → ℝ}
    (hh : ∀ k, IsPenalty (h k) (K k)) {p : ∀ k,A k → ℝ}
    (hp : ∀ k, p k ∈ stdSimplex ℝ (A k)) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ > 0, ∀ y x : ∀ k,A k → ℝ, (∀ k, IsChoice (h k) (y k) (x k)) →
      totalCoupling h p y < θ → dist x p < ε := by
  obtain ⟨θ,hθ,hbound⟩ := finite_positive_lower (fun k => K k*ε^2/8) (fun k => by have := (hh k).2.2.1; positivity)
  refine ⟨θ,hθ,fun y x hx hf => ?_⟩
  have hn : ‖x-p‖ ≤ ε/2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    have hk := (hh k).2.2.1
    have hlow := fenchel_lower_bound (hh k) (hp k) (hx k)
    have hs := norm_sub_sq_le_sqDist (p k) (x k)
    rw [norm_sub_rev] at hs
    have hfpart : fenchelCoupling (h k) (p k) (y k) ≤ totalCoupling h p y :=
      Finset.single_le_sum (fun j _ => coupling_nonneg (hh j) (hp j) (hx j)) (Finset.mem_univ k)
    have hsq : ‖x k-p k‖^2 < (ε/2)^2 := by
      apply (mul_lt_mul_iff_right₀ hk).mp
      have hmul := mul_le_mul_of_nonneg_left hs hk.le
      have hb := hbound k
      nlinarith
    have hnorm := norm_nonneg (x k-p k)
    change ‖x k-p k‖ ≤ ε/2
    nlinarith
  rw [dist_eq_norm]
  exact hn.trans_lt (by linarith)

lemma total_initial_small [∀ k, DecidableEq (A k)]
    {h : ∀ k, (A k → ℝ) → ℝ} {K : ι → ℝ} (hh : ∀ k, IsPenalty (h k) (K k))
    (a : ∀ k,A k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y x : ∀ k,A k → ℝ, (∀ k, IsChoice (h k) (y k) (x k)) →
      dist x (fun k => Pi.single (a k) 1) < δ →
      totalCoupling h (fun k => Pi.single (a k) 1) y < ε := by
  let b := ε/((Fintype.card ι:ℝ)+1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hv : ∀ k, ∃ δ > 0, ∀ y x : A k → ℝ, IsChoice (h k) y x →
      dist x (Pi.single (a k) 1) < δ → fenchelCoupling (h k) (Pi.single (a k) 1) y < b :=
    fun k => vertex_small_coupling (hh k) (a k) hb
  choose δ hδ hg using hv
  obtain ⟨D,hD,hDb⟩ := finite_positive_lower δ hδ
  refine ⟨D,hD,fun y x hx hd => ?_⟩
  have he : ∀ k, fenchelCoupling (h k) (Pi.single (a k) 1) (y k) ≤ b := by
    intro k
    apply (hg k (y k) (x k) (hx k) ?_).le
    exact ((dist_le_pi_dist x (fun j => Pi.single (a j) 1) k).trans_lt hd).trans_le (hDb k)
  have hs : totalCoupling h (fun k => Pi.single (a k) 1) y ≤ (Fintype.card ι:ℝ)*b := by
    calc
      _ ≤ ∑ _k : ι, b := Finset.sum_le_sum fun k _ => he k
      _ = _ := by simp
  have hid : b*((Fintype.card ι:ℝ)+1)=ε := div_mul_cancel₀ _ (by positivity)
  nlinarith
end StabilityProof
end

section
open Set ReinfRegGames.Extinction
namespace StabilityProof
lemma drift_bound {f v : ℝ → ℝ} {T γ : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (v t) (Ici 0) t)
    (hv : ∀ t ∈ Ioo 0 T, v t ≤ -γ) : f T ≤ f 0 - γ*T := by
  let g : ℝ → ℝ := fun t => f t + γ*t
  have hc : ContinuousOn g (Icc 0 T) := by
    intro t ht
    exact ((hf t ht.1).continuousWithinAt.mono (fun _ hh => hh.1)).add
      (continuous_const.mul continuous_id).continuousWithinAt
  have hd : ∀ t ∈ interior (Icc 0 T), HasDerivAt g (v t + γ) t := by
    intro t ht
    rw [interior_Icc] at ht
    convert ((hf t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)).add
      ((hasDerivAt_id t).const_mul γ) using 1 <;> first | rfl | simp
  have hm : AntitoneOn g (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hc
    · intro t ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t ht).deriv]
      have := hv t (by simpa only [interior_Icc] using ht)
      linarith
  have := hm ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
  dsimp [g] at this
  linarith
lemma orbit_score_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    {u : ι → (∀ k,A k) → ℝ} {h : ∀ k,(A k → ℝ) → ℝ}
    {y x : ℝ → ∀ k,A k → ℝ} (horb : IsRLOrbit u h y x) : ContinuousOn y (Ici 0) := by
  apply continuousOn_pi.mpr
  intro k
  apply continuousOn_pi.mpr
  intro a t ht
  exact ((horb t ht k).2 a).continuousWithinAt
lemma orbit_relative_drift {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    {u : ι → (∀ k,A k) → ℝ} {h : ∀ k,(A k → ℝ) → ℝ}
    {y x : ℝ → ∀ k,A k → ℝ} (horb : IsRLOrbit u h y x)
    (k : ι) (a b : A k) {T γ : ℝ} (hT : 0 ≤ T)
    (hv : ∀ t ∈ Ioo 0 T, payoffVec u (x t) k b - payoffVec u (x t) k a ≤ -γ) :
    y T k b - y T k a ≤ y 0 k b - y 0 k a - γ*T := by
  apply drift_bound hT _ hv
  intro t ht
  convert ((horb t ht k).2 b).sub ((horb t ht k).2 a) using 1 <;> first | rfl | simp
end StabilityProof
end

section
open Set
namespace StabilityProof
lemma barrier_invariant {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ici 0))
    (h0 : f 0 < c)
    (hdrop : ∀ T, 0 ≤ T → (∀ t ∈ Ioo 0 T, f t < c) → f T ≤ f 0) :
    ∀ T, 0 ≤ T → f T < c := by
  intro T hT
  by_contra hbad
  have hfc : ContinuousOn f (Icc 0 T) := hf.mono (fun _ ht => ht.1)
  have hcompact : IsCompact (Icc 0 T ∩ f ⁻¹' Ici c) :=
    hfc.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc c
  have hne : (Icc 0 T ∩ f ⁻¹' Ici c).Nonempty := ⟨T,⟨hT,le_rfl⟩,not_lt.mp hbad⟩
  obtain ⟨τ,hτ,hmin⟩ := hcompact.exists_isMinOn hne continuous_id.continuousOn
  have hbefore : ∀ t ∈ Ioo 0 τ, f t < c := by
    intro t ht
    by_contra hh
    have hm : τ ≤ t := hmin ⟨⟨ht.1.le,ht.2.le.trans hτ.1.2⟩,not_lt.mp hh⟩
    exact (not_le.mpr ht.2) hm
  have hd := hdrop τ hτ.1.1 hbefore
  exact (not_le.mpr h0) (hτ.2.trans hd)
end StabilityProof
end

section
open Finset Set Matrix ReinfRegGames.Extinction
namespace StabilityProof
open scoped BigOperators Classical
lemma transfer_simplex {B : Type*} [Fintype B] [DecidableEq B]
    {x : B → ℝ} (hx : x ∈ stdSimplex ℝ B) (a b : B) (hab : b ≠ a) :
    x + x b • (Pi.single a 1 - Pi.single b 1) ∈ stdSimplex ℝ B := by
  constructor
  · intro i
    by_cases hi : i=b
    · subst i; simp [hab]
    · by_cases hia : i=a
      · subst i; simpa [Pi.single_apply,Ne.symm hab] using add_nonneg (hx.1 a) (hx.1 b)
      · simpa [Pi.single_apply,hi,hia] using hx.1 i
  · simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Finset.sum_add_distrib,
      mul_sub,Finset.sum_sub_distrib]
    simp [Pi.single_apply,hx.2]
lemma choice_transfer_bound {B : Type*} [Fintype B] [DecidableEq B]
    {h : (B → ℝ) → ℝ} {y x : B → ℝ} (hx : IsChoice h y x)
    (a b : B) (hab : b ≠ a) {H : ℝ}
    (hH : ∀ z ∈ stdSimplex ℝ B, |h z| ≤ H) : x b*(y a-y b) ≤ 2*H := by
  let z := x + x b • (Pi.single a 1 - Pi.single b 1)
  have hz : z ∈ stdSimplex ℝ B := transfer_simplex hx.1 a b hab
  have ho := hx.2 z hz
  have hd : y ⬝ᵥ z = y ⬝ᵥ x + x b*(y a-y b) := by
    simp [z,dotProduct_add,dotProduct_smul,dotProduct_sub]
  rw [hd] at ho
  have hu := (abs_le.mp (hH z hz)).2
  have hl := (abs_le.mp (hH x hx.1)).1
  linarith
lemma coordinate_extinction {B : Type*} [Fintype B] [DecidableEq B]
    {h : (B → ℝ) → ℝ} {K : ℝ} (hh : IsPenalty h K)
    {y x : ℝ → B → ℝ} (hchoice : ∀ t, 0 ≤ t → IsChoice h (y t) (x t))
    (a b : B) (hab : b ≠ a) {γ : ℝ} (hγ : 0 < γ)
    (hscore : ∀ t, 0 ≤ t → y t b-y t a ≤ y 0 b-y 0 a-γ*t) :
    Filter.Tendsto (fun t => x t b) Filter.atTop (nhds 0) := by
  obtain ⟨H,hH0,hH⟩ := penalty_bounded hh
  rw [Metric.tendsto_atTop]
  intro ε hε
  let T := max 0 ((2*H/ε + (y 0 b-y 0 a)+1)/γ)
  refine ⟨T,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htime : 2*H/ε+(y 0 b-y 0 a)+1 ≤ γ*t := by
    have hl : (2*H/ε+(y 0 b-y 0 a)+1)/γ ≤ t := (le_max_right _ _).trans ht
    exact (div_le_iff₀ hγ).mp hl |>.trans_eq (mul_comm t γ)
  have hs := hscore t ht0
  have hx := hchoice t ht0
  have hb := choice_transfer_bound hx a b hab hH
  have hx0 := hx.1.1 b
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hx0]
  by_contra hn
  have he : ε ≤ x t b := not_lt.mp hn
  have hpos : 0 < y t a-y t b := by
    have hp : 0 ≤ 2*H/ε := by positivity
    linarith
  have hm := mul_le_mul_of_nonneg_right he hpos.le
  have hid : (2*H/ε)*ε=2*H := div_mul_cancel₀ _ (ne_of_gt hε)
  nlinarith
end StabilityProof
end

section
open Finset Set ReinfRegGames.Extinction Filter
namespace StabilityProof
open scoped BigOperators Classical
lemma profile_extinction {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    {h : ∀ k,(A k → ℝ) → ℝ} {K : ι → ℝ} (hh : ∀ k,IsPenalty (h k) (K k))
    {y x : ℝ → ∀ k,A k → ℝ} (hc : ∀ t,0≤t→∀k,IsChoice (h k) (y t k) (x t k))
    (a : ∀ k,A k) {γ : ℝ} (hγ : 0<γ)
    (hs : ∀ t,0≤t→∀k b,b≠a k→ y t k b-y t k (a k) ≤ y 0 k b-y 0 k (a k)-γ*t) :
    Tendsto x atTop (nhds (fun k => Pi.single (a k) 1)) := by
  apply tendsto_pi_nhds.mpr
  intro k
  have hcoord : ∀ b : A k,b≠a k→Tendsto (fun t => x t k b) atTop (nhds 0) := by
    intro b hb
    exact coordinate_extinction (hh k) (fun t ht => hc t ht k) (a k) b hb hγ
      (fun t ht => hs t ht k b hb)
  apply tendsto_pi_nhds.mpr
  intro b
  by_cases hb : b=a k
  · subst b
    have hsum : Tendsto (fun t => ∑ b ∈ Finset.univ.erase (a k),x t k b) atTop (nhds 0) := by
      simpa using tendsto_finsetSum (Finset.univ.erase (a k))
        (fun b hb => hcoord b (Finset.mem_erase.mp hb).1)
    have ht : Tendsto (fun t => (1:ℝ)-(∑ b ∈ Finset.univ.erase (a k),x t k b)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsum
    have he : (fun t => (1:ℝ)-(∑ b ∈ Finset.univ.erase (a k),x t k b)) =ᶠ[atTop] (fun t => x t k (a k)) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      have hh := (hc t ht k).1.2
      have hid := Finset.sum_erase_add Finset.univ (fun b => x t k b) (Finset.mem_univ (a k))
      linarith
    simpa using ht.congr' he
  · simpa [Pi.single_apply,hb] using hcoord b hb
end StabilityProof
end

section
open Finset Set ReinfRegGames.Extinction ReinfRegGames.StrictStable
namespace StabilityProof
open scoped BigOperators Classical
lemma stable_pure {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k,A k) → ℝ) (h : ∀ k,(A k → ℝ) → ℝ) (K : ι → ℝ)
    (hh : ∀ k,IsPenalty (h k) (K k)) (a : ∀ k,A k)
    (hg : ∀ k b,b≠a k→ payoffVec u (fun k => Pi.single (a k) 1) k b <
      payoffVec u (fun k => Pi.single (a k) 1) k (a k)) :
    ∀ ε > 0, ∃ δ > 0, ∀ y x : ℝ → ∀ k,A k → ℝ, IsRLOrbit u h y x →
      dist (x 0) (fun k => Pi.single (a k) 1) < δ →
      (∀ t,0≤t→dist (x t) (fun k => Pi.single (a k) 1)<ε) ∧
      Filter.Tendsto x Filter.atTop (nhds (fun k => Pi.single (a k) 1)) := by
  let p : ∀ k,A k → ℝ := fun k => Pi.single (a k) 1
  have hp : ∀ k,p k ∈ stdSimplex ℝ (A k) := fun k => single_mem_stdSimplex ℝ (a k)
  obtain ⟨r,hr,γ,hγ,hgap⟩ := uniform_payoff_gap u p a hg
  intro ε hε
  obtain ⟨θ,hθ,hcontrol⟩ := total_small_dist hh hp (lt_min hε hr)
  obtain ⟨δ,hδ,hinit⟩ := total_initial_small hh a hθ
  refine ⟨δ,hδ,?_⟩
  intro y x horb hx0
  have hchoice : ∀ t,0≤t→∀ k,IsChoice (h k) (y t k) (x t k) :=
    fun t ht k => (horb t ht k).1
  have hstart : totalCoupling h p (y 0) < θ := hinit (y 0) (x 0) (hchoice 0 le_rfl) hx0
  have hcont : ContinuousOn (fun t => totalCoupling h p (y t)) (Ici 0) :=
    (totalCoupling_continuous hh hp).comp_continuousOn (orbit_score_continuous horb)
  have hinv : ∀ T,0≤T→totalCoupling h p (y T)<θ := by
    apply barrier_invariant hcont hstart
    intro T hT hbefore
    apply Finset.sum_le_sum
    intro k _
    apply vertex_coupling_mono (hh k) (a k) (hchoice 0 le_rfl k) (hchoice T hT k)
    intro b
    by_cases hb : b=a k
    · simp [hb]
    · have hd := orbit_relative_drift horb k (a k) b hT (γ:=γ) (by
        intro t ht
        have hdist := hcontrol (y t) (x t) (hchoice t ht.1.le) (hbefore t ht)
        exact hgap (x t) (hdist.trans_le (min_le_right _ _)) k b hb)
      have hnon : 0≤γ*T := mul_nonneg hγ.le hT
      linarith
  have hnear : ∀ t,0≤t→dist (x t) p < min ε r :=
    fun t ht => hcontrol (y t) (x t) (hchoice t ht) (hinv t ht)
  constructor
  · intro t ht
    exact (hnear t ht).trans_le (min_le_left _ _)
  · apply profile_extinction hh hchoice a hγ
    intro T hT k b hb
    apply orbit_relative_drift horb k (a k) b hT
    intro t ht
    exact hgap (x t) ((hnear t ht.1.le).trans_le (min_le_right _ _)) k b hb
end StabilityProof
end

section
open ReinfRegGames.StrictStable
namespace StabilityProof
open scoped Classical
theorem full_solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (xstar : ∀ k, A k → ℝ) (hstrict : IsStrictNash u xstar) :
    IsAsymptoticallyStable u h xstar := by
  choose a ha hg using strict_nash_pure u xstar hstrict
  have hp : xstar = fun k => Pi.single (a k) 1 := funext ha
  rw [hp] at hg ⊢
  have hs := stable_pure u h K hpen a hg
  constructor
  · intro ε hε
    obtain ⟨δ,hδ,hh⟩ := hs ε hε
    exact ⟨δ,hδ,fun y x horb hx => (hh y x horb hx).1⟩
  · obtain ⟨δ,hδ,hh⟩ := hs 1 zero_lt_one
    exact ⟨δ,hδ,fun y x horb hx => (hh y x horb hx).2⟩
end StabilityProof
end

open ReinfRegGames.StrictStable

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (xstar : ∀ k, A k → ℝ) (hstrict : IsStrictNash u xstar) :
    IsAsymptoticallyStable u h xstar := by
  exact StabilityProof.full_solution u h K hpen xstar hstrict

theorem ReinfRegGames.StrictStable.theorem_5_2_iv {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (K : ι → ℝ)
    (hpen : ∀ k, ReinfRegGames.Extinction.IsPenalty (h k) (K k))
    (xstar : ∀ k, A k → ℝ) (hstrict : IsStrictNash u xstar) :
    IsAsymptoticallyStable u h xstar := by
  exact _root_.solution u h K hpen xstar hstrict
