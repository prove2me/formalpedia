-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.system10_quality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:01:14.178984+00:00
-- url     : https://prove2.me/submissions/0d52c6ca-0f45-46cc-8901-237f9d30dc12

import Definitions.Def_PolyhedralSOC_UpperBound_System10
import Definitions.Def_PolyhedralSOC_UpperBound_Tower
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace SOCTower
open Finset PolyhedralSOC PolyhedralSOC.UpperBound

lemma sum_pairs (f:ℕ→ℝ) (n:ℕ) :
    ∑i∈range (2*n),f i=∑i∈range n,(f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ]
    ring

noncomputable def foldNorm (f:ℕ→ℝ) : ℕ→ℕ→ℝ
  | 0=>f
  | n+1=>fun i=>Real.sqrt (foldNorm f n (2*i)^2+foldNorm f n (2*i+1)^2)

lemma fold_nonneg (f:ℕ→ℝ) (n:ℕ) (hn:1≤n) (i:ℕ) : 0≤foldNorm f n i := by
  cases n with
  | zero => omega
  | succ n => exact Real.sqrt_nonneg _

lemma fold_energy (f:ℕ→ℝ) (θ l:ℕ) (hl:l≤θ) :
    ∑i∈range (2^(θ-l)),foldNorm f l i^2=∑i∈range (2^θ),f i^2 := by
  induction l with
  | zero => simp [foldNorm]
  | succ l ih =>
    have hp : 2^(θ-l)=2*2^(θ-(l+1)) := by
      rw [show θ-l=(θ-(l+1))+1 by omega,pow_succ]
      omega
    have hsum : ∑i∈range (2^(θ-(l+1))),foldNorm f (l+1) i^2=
        ∑i∈range (2^(θ-l)),foldNorm f l i^2 := by
      rw [hp,sum_pairs]
      apply Finset.sum_congr rfl
      intro i hi
      exact Real.sq_sqrt (by positivity)
    exact hsum.trans (ih (by omega))

lemma fold_top (f:ℕ→ℝ) (θ:ℕ) (hθ:1≤θ) :
    foldNorm f θ 0=Real.sqrt (∑i∈range (2^θ),f i^2) := by
  have he := fold_energy f θ θ le_rfl
  simp only [Nat.sub_self,pow_zero,sum_range_one] at he
  rw [←he,Real.sqrt_sq (fold_nonneg f θ hθ 0)]

lemma exists_tower (θ:ℕ) (hθ:1≤θ) (y:Fin (2^θ)→ℝ) (t:ℝ) (hy:Shared.eucNorm y≤t) :
    ∃Y,IsTowerOf θ y t Y ∧ TowerSystem5 θ Y := by
  classical
  let f : ℕ→ℝ := fun i=>if h:i<2^θ then y ⟨i,h⟩ else 0
  have hf (i:Fin (2^θ)) : f i=y i := by simp [f]
  have he : Real.sqrt (∑i∈range (2^θ),f i^2)=Shared.eucNorm y := by
    unfold Shared.eucNorm
    rw [←Fin.sum_univ_eq_sum_range]
    congr 1
    exact Finset.sum_congr rfl (fun i _=>by rw [hf])
  let Y : ℕ→ℕ→ℝ := fun l i=>if l<θ then foldNorm f l i else t
  refine ⟨Y,⟨?_,?_⟩,?_⟩
  · intro i;simp [Y,show 0<θ by omega,foldNorm,hf]
  · simp [Y]
  · intro l hl hlθ i hi
    have hlp : l-1<θ := by omega
    have heq : l-1+1=l := by omega
    have hfrec : Real.sqrt (foldNorm f (l-1) (2*i)^2+foldNorm f (l-1) (2*i+1)^2)=foldNorm f l i := by
      rw [←heq];rfl
    simp only [Y,if_pos hlp]
    rw [hfrec]
    by_cases hlt:l<θ
    · simp [hlt]
    · have hlθ':l=θ := by omega
      subst l
      have hi0:i=0 := by simpa using hi
      subst i
      simp only [lt_self_iff_false,if_false]
      rw [fold_top f θ hθ,he]
      exact hy

noncomputable def levelNorm (θ l:ℕ) (Y:ℕ→ℕ→ℝ) : ℝ :=
  Real.sqrt (∑i∈range (2^(θ-l)),Y l i^2)

lemma level_step (θ l:ℕ) (hl:1≤l) (hlθ:l≤θ) (Y:ℕ→ℕ→ℝ) (a:ℝ) (ha:0≤a)
    (h:∀i<2^(θ-l),Real.sqrt (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2)≤a*Y l i) :
    levelNorm θ (l-1) Y≤a*levelNorm θ l Y := by
  have hp : 2^(θ-(l-1))=2*2^(θ-l) := by
    rw [show θ-(l-1)=(θ-l)+1 by omega,pow_succ]
    omega
  have hs : ∑i∈range (2^(θ-(l-1))),Y (l-1) i^2≤a^2*(∑i∈range (2^(θ-l)),Y l i^2) := by
    rw [hp,sum_pairs,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh := h i (Finset.mem_range.mp hi)
    have hn := Real.sqrt_nonneg (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2)
    have he := Real.sq_sqrt (show 0≤Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2 by positivity)
    nlinarith [sq_nonneg (a*Y l i-Real.sqrt (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2))]
  unfold levelNorm
  have he := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha] at he
  exact he

lemma quality (θ:ℕ) (hθ:1≤θ) (y:Fin (2^θ)→ℝ) (t:ℝ) (Y:ℕ→ℕ→ℝ)
    (hY:IsTowerOf θ y t Y) (a:ℕ→ℝ) (ha:∀l,1≤l → l≤θ → 0<a l)
    (h:∀l,1≤l → l≤θ → ∀i<2^(θ-l),
      Real.sqrt (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2)≤a l*Y l i) :
    Shared.eucNorm y≤(∏l∈Icc 1 θ,a l)*t := by
  have hn (l:ℕ) : 0≤levelNorm θ l Y := Real.sqrt_nonneg _
  have hp (l:ℕ) (hl:l≤θ) : 0≤∏j∈Icc 1 l,a j :=
    Finset.prod_nonneg (fun j hj=>(ha j (Finset.mem_Icc.mp hj).1 ((Finset.mem_Icc.mp hj).2.trans hl)).le)
  have hind (l:ℕ) (hl:l≤θ) : levelNorm θ 0 Y≤(∏j∈Icc 1 l,a j)*levelNorm θ l Y := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hi := ih (by omega)
      have hs := level_step θ (l+1) (by omega) hl Y (a (l+1)) (ha (l+1) (by omega) hl).le (h (l+1) (by omega) hl)
      simp only [Nat.add_sub_cancel] at hs
      have hh := mul_le_mul_of_nonneg_left hs (hp l (by omega))
      rw [Finset.prod_Icc_succ_top (by omega)]
      nlinarith
  have hbase : levelNorm θ 0 Y=Shared.eucNorm y := by
    unfold levelNorm Shared.eucNorm
    rw [Nat.sub_zero,←Fin.sum_univ_eq_sum_range]
    congr 1
    exact Finset.sum_congr rfl (fun i _=>by rw [hY.1 i])
  have ht : 0≤t := by
    have hh := h θ hθ le_rfl 0 (by simp)
    rw [hY.2] at hh
    have hpθ := ha θ hθ le_rfl
    nlinarith [Real.sqrt_nonneg (Y (θ-1) 0^2+Y (θ-1) 1^2)]
  have htop : levelNorm θ θ Y=t := by simp [levelNorm,hY.2,Real.sqrt_sq ht]
  simpa [hbase,htop] using hind θ le_rfl

end SOCTower

namespace PolyhedralSOC.UpperBound

/-- The angles `φ_j`: `φ_0` given, `φ_{j+1} = |φ_j - π/2^{j+2}|`. -/
noncomputable def aux_pae_phi (φ0 : ℝ) : ℕ → ℝ
  | 0 => φ0
  | (j+1) => |aux_pae_phi φ0 j - Real.pi / 2 ^ (j + 2)|

lemma aux_pae_phi_bound (φ0 : ℝ) (h0 : 0 ≤ φ0) (h1 : φ0 ≤ Real.pi / 2) :
    ∀ j, 0 ≤ aux_pae_phi φ0 j ∧ aux_pae_phi φ0 j ≤ Real.pi / 2 ^ (j + 1) := by
  intro j
  induction j with
  | zero => simpa [aux_pae_phi] using ⟨h0, h1⟩
  | succ k ih =>
    refine ⟨abs_nonneg _, ?_⟩
    show |aux_pae_phi φ0 k - Real.pi / 2 ^ (k + 2)| ≤ Real.pi / 2 ^ (k + 2)
    have e : Real.pi / 2 ^ (k + 1) = 2 * (Real.pi / 2 ^ (k + 2)) := by
      rw [pow_succ 2 (k + 1)]
      field_simp
    have hp : 0 ≤ Real.pi / 2 ^ (k + 2) := by positivity
    rw [abs_sub_le_iff]
    constructor <;> linarith [ih.1, ih.2]

lemma aux_pae_abs_sin (a : ℝ) (ha : |a| ≤ Real.pi) : |Real.sin a| = Real.sin |a| := by
  have h0 : 0 ≤ Real.sin |a| := Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg a) ha
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at h0 ⊢
    exact abs_of_nonneg h0
  · rw [h] at h0 ⊢
    rw [Real.sin_neg] at h0 ⊢
    exact abs_of_nonpos (by linarith)

end PolyhedralSOC.UpperBound

open PolyhedralSOC.UpperBound

theorem soc_planar_extend (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ)
    (hx : Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ x₃) :
    ∃ ξ η : ℕ → ℝ, System8 ν x₁ x₂ x₃ ξ η := by
  set z : ℂ := ⟨|x₁|, |x₂|⟩ with hz
  set r := ‖z‖ with hrdef
  have hr : r = Real.sqrt (x₁ ^ 2 + x₂ ^ 2) := by
    rw [hrdef, Complex.norm_def, hz, Complex.normSq_mk]
    congr 1
    rw [abs_mul_abs_self x₁, abs_mul_abs_self x₂]
    ring
  have hc : r * Real.cos (Complex.arg z) = |x₁| := Complex.norm_mul_cos_arg z
  have hs : r * Real.sin (Complex.arg z) = |x₂| := Complex.norm_mul_sin_arg z
  have ha0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr (abs_nonneg _)
  have ha1 : Complex.arg z ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl (abs_nonneg _))
  have hb := aux_pae_phi_bound _ ha0 ha1
  have hr0 : 0 ≤ r := norm_nonneg _
  refine ⟨fun j => r * Real.cos (aux_pae_phi (Complex.arg z) j),
    fun j => r * Real.sin (aux_pae_phi (Complex.arg z) j), ?_, ?_, ?_⟩
  · simp only [aux_pae_phi]
    exact ⟨hc.ge, hs.ge⟩
  · intro j hj1 hjν
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hφ : aux_pae_phi (Complex.arg z) (k + 1)
        = |aux_pae_phi (Complex.arg z) k - Real.pi / 2 ^ (k + 1 + 1)| := rfl
    rw [hφ]
    set φ := aux_pae_phi (Complex.arg z) k
    set θ := Real.pi / 2 ^ (k + 1 + 1)
    have hbd : |φ - θ| ≤ Real.pi := by
      have h1 := (hb (k + 1)).2
      rw [hφ] at h1
      have h2 : Real.pi / 2 ^ (k + 1 + 1) ≤ Real.pi :=
        div_le_self Real.pi_pos.le (one_le_pow₀ (by norm_num))
      exact h1.trans h2
    constructor
    · rw [Real.cos_abs, Real.cos_sub]
      ring
    · have e : -Real.sin θ * (r * Real.cos φ) + Real.cos θ * (r * Real.sin φ)
          = r * Real.sin (φ - θ) := by
        rw [Real.sin_sub]; ring
      rw [e, abs_mul, abs_of_nonneg hr0, aux_pae_abs_sin _ hbd]
  · have hbν := hb ν
    set φ := aux_pae_phi (Complex.arg z) ν
    set θ := Real.pi / 2 ^ (ν + 1)
    have hθ : θ < Real.pi / 2 := by
      have h4 : (2 : ℝ) ^ 1 < 2 ^ (ν + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by simpa using h4)
    have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    constructor
    · show r * Real.cos φ ≤ x₃
      calc r * Real.cos φ ≤ r * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) hr0
        _ = r := mul_one r
        _ ≤ x₃ := hr ▸ hx
    · show r * Real.sin φ ≤ Real.tan θ * (r * Real.cos φ)
      have htan : Real.tan φ ≤ Real.tan θ :=
        Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos], by linarith⟩
          ⟨by linarith [Real.pi_pos], hθ⟩ hbν.2
      have hsin : Real.sin φ = Real.tan φ * Real.cos φ := by
        rw [Real.tan_eq_sin_div_cos]; field_simp
      rw [hsin]
      have := mul_le_mul_of_nonneg_right htan (mul_nonneg hr0 hcos.le)
      nlinarith [this]

open PolyhedralSOC.UpperBound

private theorem theta_le (j : ℕ) (hj : 1 ≤ j) : Real.pi / 2 ^ (j + 1) ≤ Real.pi / 4 := by
  have hpi := Real.pi_pos
  have h4 : (4:ℝ) ≤ 2 ^ (j + 1) := by
    have h2 : (2:ℝ) ^ 2 ≤ 2 ^ (j + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    norm_num at h2
    exact h2
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hpi, h4]

private theorem theta_pos (j : ℕ) : 0 < Real.pi / 2 ^ (j + 1) := by
  have := Real.pi_pos; positivity

private theorem cos_pos_theta (j : ℕ) (hj : 1 ≤ j) : 0 < Real.cos (Real.pi / 2 ^ (j + 1)) := by
  have hpi := Real.pi_pos
  refine Real.cos_pos_of_mem_Ioo ⟨by linarith [theta_pos j], ?_⟩
  have h := theta_le j hj
  linarith

private theorem sin_nonneg_theta (j : ℕ) : 0 ≤ Real.sin (Real.pi / 2 ^ (j + 1)) := by
  have hpi := Real.pi_pos
  refine Real.sin_nonneg_of_nonneg_of_le_pi (theta_pos j).le ?_
  have hpow : (1:ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hpi]

theorem soc_planar_quality (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ) (ξ η : ℕ → ℝ)
    (h : System8 ν x₁ x₂ x₃ ξ η) :
    Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ (1 + delta ν) * x₃ := by
  obtain ⟨⟨h0ξ, h0η⟩, hrec, hfin1, hfin2⟩ := h
  -- the rotation invariant
  have key : ∀ j : ℕ, j ≤ ν → 0 ≤ ξ j ∧ 0 ≤ η j ∧ ξ 0 ^ 2 + η 0 ^ 2 ≤ ξ j ^ 2 + η j ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨le_trans (abs_nonneg x₁) h0ξ, le_trans (abs_nonneg x₂) h0η, le_refl _⟩
    | succ m ih =>
      intro hm
      obtain ⟨hξm, hηm, hinv⟩ := ih (by omega)
      obtain ⟨heq, hge⟩ := hrec (m + 1) (by omega) hm
      simp only [Nat.add_sub_cancel] at heq hge
      have hc := cos_pos_theta (m + 1) (by omega)
      have hs := sin_nonneg_theta (m + 1)
      have hpy : Real.sin (Real.pi / 2 ^ (m + 1 + 1)) ^ 2
          + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
      refine ⟨by rw [heq]; positivity, le_trans (abs_nonneg _) hge, ?_⟩
      have hsq : (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
          + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m) ^ 2 ≤ η (m + 1) ^ 2 := by
        have habs := hge
        have h1 : |(-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m)| ≤ η (m + 1) := hge
        nlinarith [abs_nonneg (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m),
          sq_abs (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m)]
      have hrot : ξ (m + 1) ^ 2
          + (-Real.sin (Real.pi / 2 ^ (m + 1 + 1)) * ξ m
            + Real.cos (Real.pi / 2 ^ (m + 1 + 1)) * η m) ^ 2 = ξ m ^ 2 + η m ^ 2 := by
        rw [heq]
        nlinarith [hpy]
      linarith
  obtain ⟨hξν, hην, hinvν⟩ := key ν (le_refl ν)
  have hc := cos_pos_theta ν hν
  have hs := sin_nonneg_theta ν
  have hpy : Real.sin (Real.pi / 2 ^ (ν + 1)) ^ 2 + Real.cos (Real.pi / 2 ^ (ν + 1)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  -- the endgame: `ξ ν² + η ν² ≤ (ξ ν / cos θ)²`
  have htan : Real.tan (Real.pi / 2 ^ (ν + 1))
      = Real.sin (Real.pi / 2 ^ (ν + 1)) / Real.cos (Real.pi / 2 ^ (ν + 1)) :=
    Real.tan_eq_sin_div_cos _
  have hbound : ξ ν ^ 2 + η ν ^ 2 ≤ (ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2 := by
    rw [htan] at hfin2
    have hη2 : η ν ^ 2
        ≤ (Real.sin (Real.pi / 2 ^ (ν + 1)) / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2 * ξ ν ^ 2 := by
      have hnn : 0 ≤ Real.sin (Real.pi / 2 ^ (ν + 1)) / Real.cos (Real.pi / 2 ^ (ν + 1)) :=
        div_nonneg hs hc.le
      nlinarith [hfin2, hην, hξν, mul_nonneg hnn hξν]
    rw [div_pow] at hη2
    have hc2 : (0:ℝ) < Real.cos (Real.pi / 2 ^ (ν + 1)) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2] at hη2
    rw [div_pow, le_div_iff₀ hc2]
    have hid : ξ ν ^ 2 * (Real.sin (Real.pi / 2 ^ (ν + 1)) ^ 2
        + Real.cos (Real.pi / 2 ^ (ν + 1)) ^ 2) = ξ ν ^ 2 := by rw [hpy]; ring
    nlinarith [hη2, hid]
  -- conclude
  have hx : x₁ ^ 2 + x₂ ^ 2 ≤ ξ 0 ^ 2 + η 0 ^ 2 := by
    have h1 : x₁ ^ 2 ≤ ξ 0 ^ 2 := by
      nlinarith [abs_nonneg x₁, h0ξ, sq_abs x₁]
    have h2 : x₂ ^ 2 ≤ η 0 ^ 2 := by
      nlinarith [abs_nonneg x₂, h0η, sq_abs x₂]
    linarith
  have hratio : 0 ≤ ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := div_nonneg hξν hc.le
  have hsq : Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    have hle : x₁ ^ 2 + x₂ ^ 2 ≤ (ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2 := by linarith
    calc Real.sqrt (x₁ ^ 2 + x₂ ^ 2)
        ≤ Real.sqrt ((ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1))) ^ 2) := Real.sqrt_le_sqrt hle
      _ = ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := Real.sqrt_sq hratio
  have hdel : 1 + delta ν = 1 / Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    rw [delta]; ring
  rw [hdel]
  have hxi3 : ξ ν ≤ x₃ := hfin1
  calc Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ ξ ν / Real.cos (Real.pi / 2 ^ (ν + 1)) := hsq
    _ = (1 / Real.cos (Real.pi / 2 ^ (ν + 1))) * ξ ν := by ring
    _ ≤ (1 / Real.cos (Real.pi / 2 ^ (ν + 1))) * x₃ := by
        apply mul_le_mul_of_nonneg_left hxi3 (by positivity)
namespace SOCTower
open Finset PolyhedralSOC PolyhedralSOC.UpperBound

lemma system10 (θ:ℕ) (hθ:1≤θ) (νs:ℕ→ℕ) (hν:∀l,1≤l → l≤θ → 1≤νs l) :
    (∀ (y:Fin (2^θ)→ℝ) (t:ℝ),(y,t)∈Shared.LorentzCone (2^θ) →
      ∃ (Y:ℕ→ℕ→ℝ) (ξ η:ℕ→ℕ→ℕ→ℝ),IsTowerOf θ y t Y ∧ System10 θ νs Y ξ η) ∧
    (∀ (y:Fin (2^θ)→ℝ) (t:ℝ) (Y:ℕ→ℕ→ℝ) (ξ η:ℕ→ℕ→ℕ→ℝ),
      IsTowerOf θ y t Y → System10 θ νs Y ξ η →
        Shared.eucNorm y≤(∏l∈Icc 1 θ,(1/Real.cos (Real.pi/2^(νs l+1))))*t) := by
  classical
  constructor
  · intro y t hy
    obtain ⟨Y,hY,h5⟩ := exists_tower θ hθ y t hy
    have hex : ∀l i:ℕ,∃ξ η:ℕ→ℝ,1≤l → l≤θ → i<2^(θ-l) →
        System8 (νs l) (Y (l-1) (2*i)) (Y (l-1) (2*i+1)) (Y l i) ξ η := by
      intro l i
      by_cases h:1≤l ∧ l≤θ ∧ i<2^(θ-l)
      · obtain ⟨ξ,η,hh⟩ := soc_planar_extend (νs l) (hν l h.1 h.2.1) _ _ _ (h5 l h.1 h.2.1 i h.2.2)
        exact ⟨ξ,η,fun _ _ _=>hh⟩
      · exact ⟨0,0,fun h1 h2 h3=>False.elim (h ⟨h1,h2,h3⟩)⟩
    choose ξ η hh using hex
    exact ⟨Y,ξ,η,hY,fun l h1 h2 i hi=>hh l i h1 h2 hi⟩
  · intro y t Y ξ η hY h10
    apply quality θ hθ y t Y hY (fun l=>1/Real.cos (Real.pi/2^(νs l+1)))
      (fun l h1 h2=>div_pos zero_lt_one (cos_pos_theta (νs l) (hν l h1 h2)))
    intro l h1 h2 i hi
    have hh := soc_planar_quality (νs l) (hν l h1 h2) _ _ _ _ _ (h10 l h1 h2 i hi)
    simpa [delta] using hh

end SOCTower
namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), proof of Theorem 1.1, system (10) and its
property 3, pp. 200–201 (PDF pp. 8–9): for `k = 2^θ`, `θ ≥ 1`, and positive integers
`ν_1, …, ν_θ`, the system (10) describes a polyhedral approximation of `L^k` of quality
`β = ∏_{ℓ=1}^θ 1/cos(π/2^{ν_ℓ+1}) − 1`, stated on solution sets:
(i) every `(y, t) ∈ L^k` extends to a solution of (10);
(ii) every solution of (10) satisfies `‖y‖₂ ≤ (1 + β) t`. -/
theorem _root_.solution (θ : ℕ) (hθ : 1 ≤ θ) (νs : ℕ → ℕ)
    (hν : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → 1 ≤ νs ℓ) :
    (∀ (y : Fin (2 ^ θ) → ℝ) (t : ℝ), (y, t) ∈ Shared.LorentzCone (2 ^ θ) →
      ∃ (Y : ℕ → ℕ → ℝ) (ξ η : ℕ → ℕ → ℕ → ℝ),
        IsTowerOf θ y t Y ∧ System10 θ νs Y ξ η) ∧
    (∀ (y : Fin (2 ^ θ) → ℝ) (t : ℝ) (Y : ℕ → ℕ → ℝ) (ξ η : ℕ → ℕ → ℕ → ℝ),
      IsTowerOf θ y t Y → System10 θ νs Y ξ η →
        Shared.eucNorm y ≤ (∏ ℓ ∈ Finset.Icc 1 θ, 1 / Real.cos (Real.pi / 2 ^ (νs ℓ + 1))) * t) := by
  exact SOCTower.system10 θ hθ νs hν

end PolyhedralSOC.UpperBound
