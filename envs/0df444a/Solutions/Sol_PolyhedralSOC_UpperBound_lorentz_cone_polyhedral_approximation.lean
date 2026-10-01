-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.lorentz_cone_polyhedral_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:17:32.714419+00:00
-- url     : https://prove2.me/submissions/1f45e604-211e-493c-9f92-9a2ae6ccd903

import Definitions.Def_PolyhedralSOC_UpperBound_System10
import Definitions.Def_PolyhedralSOC_UpperBound_Tower
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_PolyhedralSOC_UpperBound_System8
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone


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

theorem cos_pos_theta (j : ℕ) (hj : 1 ≤ j) : 0 < Real.cos (Real.pi / 2 ^ (j + 1)) := by
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


open PolyhedralSOC.UpperBound

-- Adapted from Shuze Chen's accepted decay proof, submission a78ca07a.
private theorem delta_bound (ν : ℕ) (hν : 1 ≤ ν) : delta ν ≤ 4 / (4 : ℝ)^ν := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi34 : Real.pi ≤ 4 := Real.pi_le_four
  have hpow : (0:ℝ) < 2 ^ (ν + 1) := by positivity
  have h4 : (4:ℝ) ≤ 2 ^ (ν + 1) := by
    have h2 : (2:ℝ) ^ 2 ≤ 2 ^ (ν + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    norm_num at h2
    exact h2
  have hθpos : 0 < Real.pi / 2 ^ (ν + 1) := by positivity
  have hθle : Real.pi / 2 ^ (ν + 1) ≤ Real.pi / 4 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) h4
  -- cos θ ≥ cos (π/3) = 1/2
  have hπ3 : Real.pi / 4 ≤ Real.pi / 3 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) (by norm_num)
  have hcosge : (1:ℝ) / 2 ≤ Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hθpos.le
      (by linarith : Real.pi / 3 ≤ Real.pi) (le_trans hθle hπ3)
    rwa [Real.cos_pi_div_three] at hmono
  have hcospos : 0 < Real.cos (Real.pi / 2 ^ (ν + 1)) := by linarith
  -- 1 - cos θ ≤ θ²/2
  have hlow : 1 - (Real.pi / 2 ^ (ν + 1)) ^ 2 / 2 ≤ Real.cos (Real.pi / 2 ^ (ν + 1)) :=
    Real.one_sub_sq_div_two_le_cos
  -- δ ν = (1 - cos θ)/cos θ ≤ 2 (1 - cos θ) ≤ θ²
  have hdelta : delta ν ≤ (Real.pi / 2 ^ (ν + 1)) ^ 2 := by
    have hd : delta ν = (1 - Real.cos (Real.pi / 2 ^ (ν + 1))) /
        Real.cos (Real.pi / 2 ^ (ν + 1)) := by
      rw [delta]
      field_simp
    rw [hd, div_le_iff₀ hcospos]
    nlinarith [hlow, hcosge, sq_nonneg (Real.pi / 2 ^ (ν + 1))]
  -- θ² = π²/4^{ν+1} ≤ 3/4^ν
  have hsq : (Real.pi / 2 ^ (ν + 1)) ^ 2 = Real.pi ^ 2 / 4 ^ (ν + 1) := by
    rw [div_pow]
    congr 1
    rw [← pow_mul]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  obtain ⟨q, hq, hqpos⟩ : ∃ q : ℝ, q = (4:ℝ) ^ ν ∧ 0 < q := ⟨4 ^ ν, rfl, by positivity⟩
  have h41 : (4:ℝ) ^ (ν + 1) = 4 * q := by rw [hq, pow_succ]; ring
  have hp16 : Real.pi ^ 2 ≤ 16 := by nlinarith [hpi, hpi34]
  rw [hsq, h41] at hdelta
  have hstep : Real.pi ^ 2 / (4 * q) ≤ 4 / q := by
    rw [div_le_div_iff₀ (by positivity) hqpos]
    nlinarith [mul_le_mul_of_nonneg_right hp16 hqpos.le]
  have hgoal : delta ν ≤ 4 / q := le_trans hdelta hstep
  rw [hq] at hgoal
  exact hgoal
private theorem cosine_positive (ν : ℕ) (hν : 1 ≤ ν) :
    0 < Real.cos (Real.pi / (2 : ℝ)^(ν+1)) := by
  have hp : (4 : ℝ) ≤ 2^(ν+1) := by
    have hh := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 2 ≤ ν+1 by omega)
    norm_num at hh ⊢
    exact hh
  have ht : Real.pi/(2 : ℝ)^(ν+1) ≤ Real.pi/3 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi/(2 : ℝ)^(ν+1) by positivity)
    (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) ht
  rw [Real.cos_pi_div_three] at hh
  linarith

private theorem choose_nu_level (ε : ℝ) (he0 : 0 < ε) (he1 : ε ≤ 1) (l : ℕ) (hl : 1 ≤ l) :
    1 ≤ ⌊16*(l : ℝ)*Real.log (2/ε)⌋₊ ∧
    1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1)) ≤ 1+ε/(2 : ℝ)^(l+1) := by
  let L := Real.log (2/ε)
  let ν := ⌊16*(l : ℝ)*L⌋₊
  have hbase : (2 : ℝ) ≤ 2/ε := (le_div_iff₀ he0).mpr (by linarith)
  have hL : (1 : ℝ)/2 ≤ L := by
    have hh := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hbase
    have hlog := Real.log_two_gt_d9
    dsimp [L]
    linarith
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : 1 ≤ 16*(l : ℝ)*L := by nlinarith [mul_le_mul_of_nonneg_right hlR (show 0 ≤ L by linarith)]
  have hν : 1 ≤ ν := Nat.floor_pos.mpr hx
  refine ⟨hν,?_⟩
  have hfloor := Nat.lt_floor_add_one (16*(l : ℝ)*L)
  have hνlow : ((l+3 : ℕ) : ℝ)*L ≤ (ν : ℝ) := by
    have hh : (l : ℝ)*L ≥ L := by nlinarith [mul_nonneg (sub_nonneg.mpr hlR) (le_trans (by norm_num) hL)]
    simp only [Nat.cast_add,Nat.cast_ofNat] at *
    dsimp [ν]
    nlinarith
  have hexp : Real.exp ((ν : ℝ)) ≤ (4 : ℝ)^ν := by
    have hh := pow_le_pow_left₀ (Real.exp_pos 1).le (show Real.exp 1 ≤ 4 by linarith [Real.exp_one_lt_three]) ν
    rw [← Real.exp_nat_mul] at hh
    simpa using hh
  have hνpow : (2/ε)^(l+3) ≤ (4 : ℝ)^ν := by
    calc
      _ = Real.exp (((l+3 : ℕ) : ℝ)*L) := by rw [Real.exp_nat_mul,Real.exp_log (by positivity : (0 : ℝ) < 2/ε)]
      _ ≤ Real.exp (ν : ℝ) := Real.exp_le_exp.mpr hνlow
      _ ≤ _ := hexp
  have hlow : (2/ε)*(2 : ℝ)^(l+2) ≤ (4 : ℝ)^ν := by
    have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hbase (l+2)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2/ε by positivity)
    calc
      _ ≤ (2/ε)*(2/ε)^(l+2) := hh'
      _ = (2/ε)^(l+3) := by rw [show l+3=(l+2)+1 by omega,pow_succ];ring
      _ ≤ _ := hνpow
  have hd := delta_bound ν hν
  have hdsmall : 4/(4 : ℝ)^ν ≤ ε/(2 : ℝ)^(l+1) := by
    have hq : 0 < (2/ε)*(2 : ℝ)^(l+2) := by positivity
    calc
      _ ≤ 4/((2/ε)*(2 : ℝ)^(l+2)) := div_le_div_of_nonneg_left (by norm_num) hq hlow
      _ = _ := by rw [show l+2=(l+1)+1 by omega,pow_succ];field_simp;ring
  unfold delta at hd
  change 1/Real.cos (Real.pi/(2 : ℝ)^(ν+1)) ≤ _
  linarith

private theorem weighted_levels (θ : ℕ) :
    (∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ-l)*(l : ℝ))=2^(θ+1)-(θ : ℝ)-2 := by
  induction θ with
  | zero => norm_num
  | succ θ ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ θ+1 by omega)]
    have he : (∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ+1-l)*(l : ℝ))=
        2*(∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ-l)*(l : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hlt := (Finset.mem_Icc.mp hl).2
      rw [show θ+1-l=(θ-l)+1 by omega,pow_succ]
      ring
    simp only [Nat.succ_eq_add_one,Nat.sub_self,pow_zero,one_mul] at *
    rw [he,ih,pow_succ]
    push_cast
    ring
private theorem product_levels (ε : ℝ) (he0 : 0 < ε) (he1 : ε ≤ 1) :
    ∀ θ : ℕ,0 ≤ (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1))) ∧
      (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1))) ≤
        1+ε*(1-1/(2 : ℝ)^θ) := by
  intro θ
  induction θ with
  | zero => norm_num
  | succ θ ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ θ+1 by omega)]
    have hlevel := choose_nu_level ε he0 he1 (θ+1) (by omega)
    have hfac : 0 ≤ 1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*((θ+1 : ℕ) : ℝ)*Real.log (2/ε)⌋₊+1)) :=
      le_of_lt (one_div_pos.mpr (cosine_positive _ hlevel.1))
    refine ⟨mul_nonneg ih.1 hfac,?_⟩
    have htwo : (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1))) ≤ 2 := by
      have hh : 0 ≤ ε*(1/(2 : ℝ)^θ) := by positivity
      nlinarith [ih.2]
    have hmul := mul_le_mul_of_nonneg_left hlevel.2 ih.1
    have htwo' := mul_le_mul_of_nonneg_right htwo (show 0 ≤ ε/(2 : ℝ)^((θ+1)+1) by positivity)
    calc
      _ ≤ (1+ε*(1-1/(2 : ℝ)^θ))+2*(ε/(2 : ℝ)^((θ+1)+1)) := by nlinarith [ih.2]
      _ = 1+ε*(1-1/(2 : ℝ)^(θ+1)) := by
        rw [pow_succ,pow_succ]
        field_simp
        ring

theorem soc_choice :
    ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,0 < C ∧
      ∀ θ : ℕ,1 ≤ θ → ∀ ε : ℝ,0 < ε → ε ≤ 1 →
        (∀ l : ℕ,1 ≤ l → l ≤ θ → 1 ≤ ⌊c*l*Real.log (2/ε)⌋₊) ∧
        (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/2^(⌊c*l*Real.log (2/ε)⌋₊+1)))-1 ≤ ε ∧
        ((∑ l∈Finset.Icc 1 θ,2^(θ-l)*⌊c*l*Real.log (2/ε)⌋₊ : ℕ) : ℝ) ≤ C*2^θ*Real.log (2/ε) := by
  refine ⟨16,by norm_num,32,by norm_num,?_⟩
  intro θ hθ ε he0 he1
  refine ⟨fun l hl hlt => (choose_nu_level ε he0 he1 l hl).1,?_,?_⟩
  · have hh := (product_levels ε he0 he1 θ).2
    have hn : 0 ≤ ε*(1/(2 : ℝ)^θ) := by positivity
    nlinarith
  · have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he0).mpr (by linarith))
    simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    calc
      _ ≤ 16*Real.log (2/ε)*(∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ-l)*(l : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        have hf := Nat.floor_le (show 0 ≤ 16*(l : ℝ)*Real.log (2/ε) by positivity)
        have hh := mul_le_mul_of_nonneg_left hf (show 0 ≤ (2 : ℝ)^(θ-l) by positivity)
        nlinarith
      _ ≤ 16*Real.log (2/ε)*(2 : ℝ)^(θ+1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [weighted_levels]
        have hh : (0 : ℝ) ≤ θ := Nat.cast_nonneg θ
        linarith
      _ = 32*(2 : ℝ)^θ*Real.log (2/ε) := by rw [pow_succ];ring


open Finset
namespace SOCCount

abbrev Block (θ : ℕ) := Σ l : Fin θ,Fin (2^(θ-(l.val+1)))
abbrev Aux (θ : ℕ) (ν : ℕ → ℕ) := Block θ ⊕ Σ b : Block θ,Bool×Fin (ν (b.1.val+1)+1)
abbrev Con (θ : ℕ) (ν : ℕ → ℕ) := Bool ⊕ Σ b : Block θ,Fin 4 ⊕ ((Fin (ν (b.1.val+1))×Fin 4) ⊕ Fin 2)



theorem block_card_succ (θ : ℕ) : Fintype.card (Block (θ+1))=2^θ+Fintype.card (Block θ) := by
  simp only [Block,Fintype.card_sigma,Fintype.card_fin,Fin.sum_univ_succ,Fin.val_zero,zero_add,Nat.add_sub_cancel,Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

theorem block_card_add_one (θ : ℕ) : Fintype.card (Block θ)+1=2^θ := by
  induction θ with
  | zero => simp [Block]
  | succ θ ih => rw [block_card_succ,pow_succ];omega

theorem block_card_le (θ : ℕ) : Fintype.card (Block θ) ≤ 2^θ := by
  have h:=block_card_add_one θ
  omega

theorem block_sum (θ : ℕ) (ν : ℕ → ℕ) :
    (∑ b : Block θ,ν (b.1.val+1))=∑ l∈Finset.Icc 1 θ,2^(θ-l)*ν l := by
  change (∑ b : Σ l : Fin θ,Fin (2^(θ-(l.val+1))),ν (b.1.val+1)) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Finset.sum_bij (fun i _=>i.val+1)
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨by omega,by have :=i.isLt;omega⟩
  · intro i hi j hj he
    apply Fin.ext
    omega
  · intro j hj
    have hj1:=Finset.mem_Icc.mp hj
    exact ⟨⟨j-1,by omega⟩,Finset.mem_univ _,by dsimp;omega⟩
  · intro i hi
    rfl

theorem total_card_eq (θ : ℕ) (ν : ℕ → ℕ) :
    Fintype.card (Aux θ ν)+Fintype.card (Con θ ν)=
      2+9*Fintype.card (Block θ)+6*(∑ b : Block θ,ν (b.1.val+1)) := by
  simp only [Aux,Con,Fintype.card_sum,Fintype.card_sigma,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_fin,Nat.mul_add,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  ring

theorem total_card_le (θ : ℕ) (ν : ℕ → ℕ) :
    Fintype.card (Aux θ ν)+Fintype.card (Con θ ν) ≤
      2+9*2^θ+6*(∑ l∈Finset.Icc 1 θ,2^(θ-l)*ν l) := by
  rw [total_card_eq,block_sum]
  have h:=block_card_le θ
  omega

end SOCCount


namespace SOCEmbedding

theorem dyadic_dimension (k : ℕ) (hk : 1 ≤ k) :
    ∃ θ : ℕ,1 ≤ θ ∧ k ≤ 2^θ ∧ 2^θ ≤ 2*k := by
  refine ⟨Nat.log 2 k+1,by omega,?_,?_⟩
  · exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k).le
  · have hh := Nat.pow_log_le_self 2 (show k ≠ 0 by omega)
    rw [pow_succ]
    omega

def pad (k N : ℕ) (y : Fin k → ℝ) (i : Fin N) : ℝ :=
  if h : i.val < k then y ⟨i.val,h⟩ else 0

def padLinear (k N : ℕ) : (Fin k → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun := pad k N
  map_add' := by
    intro x y
    funext i
    simp only [pad,Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c y
    funext i
    simp only [pad,Pi.smul_apply]
    split_ifs <;> simp

theorem pad_apply (k N : ℕ) (y : Fin k → ℝ) (i : Fin N) :
    padLinear k N y i=if h : i.val < k then y ⟨i.val,h⟩ else 0 := rfl

theorem sum_sq_pad {k N : ℕ} (hkN : k ≤ N) (y : Fin k → ℝ) :
    (∑ i : Fin N,(pad k N y i)^2)=∑ i : Fin k,(y i)^2 := by
  let f : ℕ → ℝ := fun i => if h : i < k then (y ⟨i,h⟩)^2 else 0
  have hN : (∑ i : Fin N,(pad k N y i)^2)=∑ i∈Finset.range N,f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [pad,f]
    split_ifs <;> simp
  have hk : (∑ i : Fin k,(y i)^2)=∑ i∈Finset.range k,f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f,i.isLt]
  rw [hN,hk]
  symm
  apply Finset.sum_subset (Finset.range_mono hkN)
  intro i hi hnot
  have hn : ¬i < k := by simpa only [Finset.mem_range] using hnot
  simp [f,hn]

theorem eucNorm_pad {k N : ℕ} (hkN : k ≤ N) (y : Fin k → ℝ) :
    PolyhedralSOC.Shared.eucNorm (pad k N y)=PolyhedralSOC.Shared.eucNorm y := by
  unfold PolyhedralSOC.Shared.eucNorm
  rw [sum_sq_pad hkN]

theorem eucNorm_padLinear {k N : ℕ} (hkN : k ≤ N) (y : Fin k → ℝ) :
    PolyhedralSOC.Shared.eucNorm (padLinear k N y)=PolyhedralSOC.Shared.eucNorm y :=
  eucNorm_pad hkN y

end SOCEmbedding



namespace SOCEncoding
open SOCCount PolyhedralSOC PolyhedralSOC.UpperBound
abbrev Input (k θ:ℕ) (ν:ℕ→ℕ) := (Fin k→ℝ) × ℝ × (Aux θ ν→ℝ)

noncomputable def yAt {k θ:ℕ} {ν:ℕ→ℕ} (i:ℕ) : Input k θ ν→ₗ[ℝ]ℝ :=
  if h:i<k then (LinearMap.proj (⟨i,h⟩:Fin k)).comp (LinearMap.fst ℝ _ _) else 0
noncomputable def tAt {k θ:ℕ} {ν:ℕ→ℕ} : Input k θ ν→ₗ[ℝ]ℝ :=
  (LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)
noncomputable def uAt {k θ:ℕ} {ν:ℕ→ℕ} (a:Aux θ ν) : Input k θ ν→ₗ[ℝ]ℝ :=
  (LinearMap.proj a).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))

def blockOf (θ l i:ℕ) (hl:1≤l ∧ l≤θ ∧ i<2^(θ-l)) : Block θ :=
  ⟨⟨l-1,by omega⟩,⟨i,by simpa [Nat.sub_add_cancel hl.1] using hl.2.2⟩⟩

noncomputable def node {k θ:ℕ} {ν:ℕ→ℕ} (l i:ℕ) : Input k θ ν→ₗ[ℝ]ℝ :=
  if l=0 then yAt i else if h:1≤l ∧ l≤θ ∧ i<2^(θ-l) then uAt (.inl (blockOf θ l i h)) else 0

noncomputable def xi {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) (j:Fin (ν (b.1.val+1)+1)) : Input k θ ν→ₗ[ℝ]ℝ :=
  uAt (.inr ⟨b,(false,j)⟩)
noncomputable def eta {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) (j:Fin (ν (b.1.val+1)+1)) : Input k θ ν→ₗ[ℝ]ℝ :=
  uAt (.inr ⟨b,(true,j)⟩)

noncomputable def constraint {k θ:ℕ} {ν:ℕ→ℕ} (c:Con θ ν) : Input k θ ν→ₗ[ℝ]ℝ :=
  match c with
  | .inl sign=>if sign then node θ 0-tAt else tAt-node θ 0
  | .inr ⟨b,.inl j⟩=>
    ![xi b 0-node b.1.val (2*b.2.val),xi b 0+node b.1.val (2*b.2.val),
      eta b 0-node b.1.val (2*b.2.val+1),eta b 0+node b.1.val (2*b.2.val+1)] j
  | .inr ⟨b,.inr (.inl (j,r))⟩=>
    let c := Real.cos (Real.pi/2^(j.val+2))
    let s := Real.sin (Real.pi/2^(j.val+2))
    let d := xi b j.succ-c • xi b j.castSucc-s • eta b j.castSucc
    let e := (-s) • xi b j.castSucc+c • eta b j.castSucc
    ![d,-d,eta b j.succ-e,eta b j.succ+e] r
  | .inr ⟨b,.inr (.inr r)⟩=>
    ![node (b.1.val+1) b.2.val-xi b (Fin.last _),
      Real.tan (Real.pi/2^(ν (b.1.val+1)+1)) • xi b (Fin.last _)-eta b (Fin.last _)] r

noncomputable def Xi {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) (z:Input k θ ν) (j:ℕ) : ℝ :=
  if h:j≤ν (b.1.val+1) then xi b ⟨j,by omega⟩ z else 0
noncomputable def Eta {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) (z:Input k θ ν) (j:ℕ) : ℝ :=
  if h:j≤ν (b.1.val+1) then eta b ⟨j,by omega⟩ z else 0

lemma node_zero {k θ:ℕ} {ν:ℕ→ℕ} (i:ℕ) : (node 0 i:Input k θ ν→ₗ[ℝ]ℝ)=yAt i := by simp [node]
lemma node_block {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) :
    (node (b.1.val+1) b.2.val:Input k θ ν→ₗ[ℝ]ℝ)=uAt (.inl b) := by
  have h : 1≤b.1.val+1 ∧ b.1.val+1≤θ ∧ b.2.val<2^(θ-(b.1.val+1)) := ⟨by omega,by omega,b.2.isLt⟩
  simp only [node,Nat.add_one_ne_zero,if_false,dif_pos h]
  congr 1

lemma xi_eq {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) (z:Input k θ ν) (j:Fin (ν (b.1.val+1)+1)) : Xi b z j=xi b j z := by
  simp [Xi,show j.val≤ν (b.1.val+1) by omega]
lemma eta_eq {k θ:ℕ} {ν:ℕ→ℕ} (b:Block θ) (z:Input k θ ν) (j:Fin (ν (b.1.val+1)+1)) : Eta b z j=eta b j z := by
  simp [Eta,show j.val≤ν (b.1.val+1) by omega]

lemma constraints_iff {k θ:ℕ} {ν:ℕ→ℕ} (z:Input k θ ν) :
    (∀c:Con θ ν,0≤constraint c z) ↔ node θ 0 z=tAt z ∧
      ∀b:Block θ,System8 (ν (b.1.val+1)) (node b.1.val (2*b.2.val) z)
        (node b.1.val (2*b.2.val+1) z) (node (b.1.val+1) b.2.val z) (Xi b z) (Eta b z) := by
  constructor
  · intro h
    have h0 := h (.inl false)
    have h1 := h (.inl true)
    simp only [constraint,Bool.false_eq_true,if_false,if_true,LinearMap.sub_apply] at h0 h1
    refine ⟨by linarith,?_⟩
    intro b
    have hi (j:Fin 4) := h (.inr ⟨b,.inl j⟩)
    have ht (j:Fin 2) := h (.inr ⟨b,.inr (.inr j)⟩)
    simp only [constraint] at hi ht
    have hx0 := xi_eq b z (0:Fin (ν (b.1.val+1)+1))
    have he0 := eta_eq b z (0:Fin (ν (b.1.val+1)+1))
    have hxn := xi_eq b z (Fin.last (ν (b.1.val+1)))
    have hen := eta_eq b z (Fin.last (ν (b.1.val+1)))
    refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
    · rw [show Xi b z 0=xi b 0 z from hx0]
      apply abs_le.mpr
      have hi0:=hi 0;have hi1:=hi 1
      simp at hi0 hi1
      constructor <;> linarith
    · rw [show Eta b z 0=eta b 0 z from he0]
      apply abs_le.mpr
      have hi2:=hi 2;have hi3:=hi 3
      simp at hi2 hi3
      constructor <;> linarith
    · intro j hj hνj
      let jj : Fin (ν (b.1.val+1)) := ⟨j-1,by omega⟩
      have hsuc : jj.val+1=j := by dsimp [jj];omega
      have hr (r:Fin 4) := h (.inr ⟨b,.inr (.inl (jj,r))⟩)
      simp only [constraint] at hr
      have hxx := xi_eq b z jj.succ
      have hxp := xi_eq b z jj.castSucc
      have hex := eta_eq b z jj.succ
      have hep := eta_eq b z jj.castSucc
      have h0:=hr 0;have h1:=hr 1;have h2:=hr 2;have h3:=hr 3
      dsimp at h0 h1 h2 h3
      change Xi b z j=Real.cos (Real.pi/2^(j+1))*Xi b z (j-1)+Real.sin (Real.pi/2^(j+1))*Eta b z (j-1) ∧ _
      simp only [Fin.val_succ,Fin.val_castSucc,hsuc] at hxx hex
      have ha : jj.val+2=j+1 := by omega
      change Xi b z (j-1)=xi b jj.castSucc z at hxp
      change Eta b z (j-1)=eta b jj.castSucc z at hep
      rw [ha] at h0 h1 h2 h3
      rw [hxx,hxp,hep,hex]
      constructor
      · linarith
      · apply abs_le.mpr;constructor <;> linarith
    · have h0:=ht 0
      simp at h0
      change Xi b z (ν (b.1.val+1))≤_
      rw [show Xi b z (ν (b.1.val+1))=xi b (Fin.last _) z from hxn]
      linarith
    · have h1:=ht 1
      simp at h1
      change Eta b z (ν (b.1.val+1))≤_
      rw [show Eta b z (ν (b.1.val+1))=eta b (Fin.last _) z from hen,
        show Xi b z (ν (b.1.val+1))=xi b (Fin.last _) z from hxn]
      linarith
  · rintro ⟨he,h⟩ c
    cases c with
    | inl sign => cases sign <;> simp [constraint,he]
    | inr c =>
      obtain ⟨b,c⟩ := c
      obtain ⟨⟨hi1,hi2⟩,hr,ht1,ht2⟩ := h b
      cases c with
      | inl r =>
        have h0:=xi_eq b z (0:Fin (ν (b.1.val+1)+1))
        have h1:=eta_eq b z (0:Fin (ν (b.1.val+1)+1))
        change Xi b z 0=xi b 0 z at h0
        change Eta b z 0=eta b 0 z at h1
        rw [h0] at hi1
        rw [h1] at hi2
        have ha:=abs_le.mp hi1;have hb:=abs_le.mp hi2
        fin_cases r <;> dsimp [constraint] <;> linarith
      | inr c => cases c with
        | inl c =>
          obtain ⟨j,r⟩ := c
          have hh:=hr (j.val+1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at hh
          rw [show Xi b z (j.val+1)=xi b j.succ z from xi_eq b z j.succ,
            show Xi b z j.val=xi b j.castSucc z from xi_eq b z j.castSucc,
            show Eta b z (j.val+1)=eta b j.succ z from eta_eq b z j.succ,
            show Eta b z j.val=eta b j.castSucc z from eta_eq b z j.castSucc] at hh
          simp only [Nat.add_assoc,show (1:ℕ)+1=2 by omega] at hh
          have ha:=abs_le.mp hh.2
          fin_cases r <;> dsimp [constraint] <;> nlinarith [hh.1]
        | inr r =>
          rw [show Xi b z (ν (b.1.val+1))=xi b (Fin.last _) z from xi_eq b z (Fin.last _)] at ht1 ht2
          rw [show Eta b z (ν (b.1.val+1))=eta b (Fin.last _) z from eta_eq b z (Fin.last _)] at ht2
          fin_cases r <;> dsimp [constraint] <;> linarith

noncomputable def encode {θ:ℕ} {ν:ℕ→ℕ} (Y:ℕ→ℕ→ℝ) (ξ η:ℕ→ℕ→ℕ→ℝ) : Aux θ ν→ℝ
  | .inl b=>Y (b.1.val+1) b.2.val
  | .inr ⟨b,(sign,j)⟩=>if sign then η (b.1.val+1) b.2.val j else ξ (b.1.val+1) b.2.val j

lemma node_encode {k θ:ℕ} {ν:ℕ→ℕ} (y:Fin k→ℝ) (t:ℝ) (Y:ℕ→ℕ→ℝ) (ξ η:ℕ→ℕ→ℕ→ℝ)
    (hY:∀i:Fin (2^θ),Y 0 i=SOCEmbedding.pad k (2^θ) y i)
    (l i:ℕ) (hl:l≤θ) (hi:i<2^(θ-l)) :
    node l i (y,t,encode (θ:=θ) (ν:=ν) Y ξ η)=Y l i := by
  by_cases h0:l=0
  · subst l
    have hh:=hY ⟨i,by simpa using hi⟩
    by_cases hik:i<k <;> simpa [node,yAt,SOCEmbedding.pad,hik] using hh.symm
  · have hb:1≤l ∧ l≤θ ∧ i<2^(θ-l):=⟨by omega,hl,hi⟩
    simp only [node,if_neg h0,dif_pos hb]
    simp [uAt,encode,blockOf,Nat.sub_add_cancel hb.1]

lemma system8_congr (ν:ℕ) (x y t:ℝ) (ξ η ξ' η':ℕ→ℝ)
    (hξ:∀j,j≤ν→ξ j=ξ' j) (hη:∀j,j≤ν→η j=η' j) :
    System8 ν x y t ξ η ↔ System8 ν x y t ξ' η' := by
  have step (ξ η ξ' η':ℕ→ℝ) (hx:∀j,j≤ν→ξ j=ξ' j) (he:∀j,j≤ν→η j=η' j)
      (h:System8 ν x y t ξ η) : System8 ν x y t ξ' η' := by
    rcases h with ⟨hi,hr,hf⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [hx 0 (Nat.zero_le _),he 0 (Nat.zero_le _)] using hi
    · intro j hj hjν
      simpa only [hx j hjν,he j hjν,hx (j-1) (by omega),he (j-1) (by omega)] using hr j hj hjν
    · simpa only [hx ν le_rfl,he ν le_rfl] using hf
  exact ⟨step ξ η ξ' η' hξ hη,step ξ' η' ξ η (fun j hj=>(hξ j hj).symm) (fun j hj=>(hη j hj).symm)⟩

lemma encode_feasible {k θ:ℕ} {ν:ℕ→ℕ} (hθ:1≤θ) (y:Fin k→ℝ) (t:ℝ)
    (Y:ℕ→ℕ→ℝ) (ξ η:ℕ→ℕ→ℕ→ℝ)
    (hY:IsTowerOf θ (SOCEmbedding.pad k (2^θ) y) t Y) (hs:System10 θ ν Y ξ η) :
    ∀c:Con θ ν,0≤constraint c (y,t,encode Y ξ η) := by
  apply (constraints_iff _).mpr
  constructor
  · rw [node_encode y t Y ξ η hY.1 θ 0 le_rfl (by simp)]
    exact hY.2
  · intro b
    have hl:b.1.val+1≤θ:=by omega
    have hc:2^(θ-b.1.val)=2*2^(θ-(b.1.val+1)):=by
      rw [show θ-b.1.val=θ-(b.1.val+1)+1 by omega,pow_succ];ring
    rw [node_encode y t Y ξ η hY.1 _ _ (by omega) (by rw [hc];omega),
      node_encode y t Y ξ η hY.1 _ _ (by omega) (by rw [hc];omega),
      node_encode y t Y ξ η hY.1 _ _ hl b.2.isLt]
    have hh:=hs (b.1.val+1) (by omega) hl b.2.val b.2.isLt
    simp only [Nat.add_sub_cancel] at hh
    apply (system8_congr _ _ _ _ _ _ _ _ ?_ ?_).mp hh
    · intro j hj
      simp [Xi,xi,uAt,encode,hj]
    · intro j hj
      simp [Eta,eta,uAt,encode,hj]

lemma decode_tower {k θ:ℕ} {ν:ℕ→ℕ} (y:Fin k→ℝ) (t:ℝ) (u:Aux θ ν→ℝ)
    (h:∀c:Con θ ν,0≤constraint c (y,t,u)) :
    IsTowerOf θ (SOCEmbedding.pad k (2^θ) y) t (fun l i=>node l i (y,t,u)) := by
  constructor
  · intro i
    by_cases hi:i.val<k <;> simp [node,yAt,SOCEmbedding.pad,hi]
  · exact ((constraints_iff _).mp h).1

lemma decode_blocks {k θ:ℕ} {ν:ℕ→ℕ} (z:Input k θ ν)
    (h:∀c:Con θ ν,0≤constraint c z) (l i:ℕ) (hl:1≤l) (hlθ:l≤θ) (hi:i<2^(θ-l)) :
    ∃ξ η:ℕ→ℝ,System8 (ν l) (node (l-1) (2*i) z) (node (l-1) (2*i+1) z) (node l i z) ξ η := by
  let b:=blockOf θ l i ⟨hl,hlθ,hi⟩
  have hb: b.1.val+1=l := by simp [b,blockOf,Nat.sub_add_cancel hl]
  have hh:=((constraints_iff z).mp h).2 b
  refine ⟨Xi b z,Eta b z,?_⟩
  simpa only [b,blockOf,Nat.sub_add_cancel hl] using hh

end SOCEncoding


namespace SOCMain
open PolyhedralSOC PolyhedralSOC.UpperBound SOCCount SOCEncoding Finset

lemma feasible_quality {k θ:ℕ} {ν:ℕ→ℕ} (hθ:1≤θ) (hk:k≤2^θ)
    (hν:∀l,1≤l→l≤θ→1≤ν l) (y:Fin k→ℝ) (t:ℝ) (u:Aux θ ν→ℝ)
    (h:∀c:Con θ ν,0≤constraint c (y,t,u)) :
    Shared.eucNorm y ≤ (∏l∈Icc 1 θ,(1/Real.cos (Real.pi/2^(ν l+1))))*t := by
  rw [← SOCEmbedding.eucNorm_pad hk y]
  apply SOCTower.quality θ hθ (SOCEmbedding.pad k (2^θ) y) t
    (fun l i=>node l i (y,t,u)) (decode_tower y t u h)
    (fun l=>1/Real.cos (Real.pi/2^(ν l+1)))
    (fun l h1 h2=>div_pos zero_lt_one (cos_pos_theta _ (hν l h1 h2)))
  intro l h1 h2 i hi
  obtain ⟨ξ,η,hh⟩:=decode_blocks (y,t,u) h l i h1 h2 hi
  have hq:=soc_planar_quality (ν l) (hν l h1 h2) _ _ _ _ _ hh
  simpa [delta] using hq

lemma finite_encoding {k θ:ℕ} {ν:ℕ→ℕ} (ε:ℝ)
    (hf:∀(y:Fin k→ℝ) (t:ℝ),(y,t)∈Shared.LorentzCone k→∃u:Aux θ ν→ℝ,∀c:Con θ ν,0≤constraint c (y,t,u))
    (hb:∀(y:Fin k→ℝ) (t:ℝ) (u:Aux θ ν→ℝ),(∀c:Con θ ν,0≤constraint c (y,t,u))→Shared.eucNorm y≤(1+ε)*t) :
    ∃P:(Fin k→ℝ)×ℝ×(Fin (Fintype.card (Aux θ ν))→ℝ)→ₗ[ℝ](Fin (Fintype.card (Con θ ν))→ℝ),
      Shared.IsPolyhedralApprox k (Fintype.card (Aux θ ν)) (Fintype.card (Con θ ν)) ε P := by
  classical
  let eA:=Fintype.equivFin (Aux θ ν)
  let eC:=Fintype.equivFin (Con θ ν)
  let R:((Fin k→ℝ)×ℝ×(Fin (Fintype.card (Aux θ ν))→ℝ))→ₗ[ℝ]Input k θ ν:=
    {toFun:=fun z=>(z.1,z.2.1,fun a=>z.2.2 (eA a)),map_add':=by intros;rfl,map_smul':=by intros;rfl}
  let P:=LinearMap.pi (fun j:Fin (Fintype.card (Con θ ν))=>(constraint (eC.symm j)).comp R)
  refine ⟨P,?_,?_⟩
  · intro y t hy
    obtain ⟨u,hu⟩:=hf y t hy
    refine ⟨fun j=>u (eA.symm j),?_⟩
    intro j
    simpa [P,R] using hu (eC.symm j)
  · intro y t u hu
    apply hb y t (fun a=>u (eA a))
    intro c
    simpa [P,R] using hu (eC c)

lemma approximation (k θ:ℕ) (ν:ℕ→ℕ) (ε:ℝ) (hθ:1≤θ) (hk:k≤2^θ)
    (hν:∀l,1≤l→l≤θ→1≤ν l)
    (hε:(∏l∈Icc 1 θ,(1/Real.cos (Real.pi/2^(ν l+1))))-1≤ε) :
    ∃P:(Fin k→ℝ)×ℝ×(Fin (Fintype.card (Aux θ ν))→ℝ)→ₗ[ℝ](Fin (Fintype.card (Con θ ν))→ℝ),
      Shared.IsPolyhedralApprox k (Fintype.card (Aux θ ν)) (Fintype.card (Con θ ν)) ε P := by
  apply finite_encoding ε
  · intro y t hy
    have hp:(SOCEmbedding.pad k (2^θ) y,t)∈Shared.LorentzCone (2^θ):=by
      change Shared.eucNorm (SOCEmbedding.pad k (2^θ) y)≤t
      rw [SOCEmbedding.eucNorm_pad hk]
      exact hy
    obtain ⟨Y,ξ,η,hY,hs⟩:=(SOCTower.system10 θ hθ ν hν).1 _ t hp
    exact ⟨encode Y ξ η,encode_feasible hθ y t Y ξ η hY hs⟩
  · intro y t u hu
    have hq:=feasible_quality hθ hk hν y t u hu
    have hpos:0<(∏l∈Icc 1 θ,(1/Real.cos (Real.pi/2^(ν l+1)))):=by
      apply Finset.prod_pos
      intro l hl
      exact div_pos zero_lt_one (cos_pos_theta _ (hν l (mem_Icc.mp hl).1 (mem_Icc.mp hl).2))
    have ht:0≤t:=by
      have hn:0≤Shared.eucNorm y:=Real.sqrt_nonneg _
      exact nonneg_of_mul_nonneg_right (hn.trans hq) hpos
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith : (∏l∈Icc 1 θ,(1/Real.cos (Real.pi/2^(ν l+1))))≤1+ε) ht)

theorem upper_bound :
    ∃C:ℝ,0<C ∧∀k:ℕ,1≤k→∀ε:ℝ,0<ε→ε≤1→
      ∃p q:ℕ,∃P:(Fin k→ℝ)×ℝ×(Fin p→ℝ)→ₗ[ℝ](Fin q→ℝ),
        Shared.IsPolyhedralApprox k p q ε P ∧ ((p+q:ℕ):ℝ)≤C*k*Real.log (2/ε) := by
  obtain ⟨c,hc,C,hC,hchoice⟩:=soc_choice
  refine ⟨2*(22+6*C),by positivity,?_⟩
  intro k hk ε he0 he1
  obtain ⟨θ,hθ,hkN,hNk⟩:=SOCEmbedding.dyadic_dimension k hk
  let ν:ℕ→ℕ:=fun l=>⌊c*l*Real.log (2/ε)⌋₊
  obtain ⟨hν,he,hW⟩:=hchoice θ hθ ε he0 he1
  obtain ⟨P,hP⟩:=approximation k θ ν ε hθ hkN hν he
  refine ⟨Fintype.card (Aux θ ν),Fintype.card (Con θ ν),P,hP,?_⟩
  have hdim:=SOCCount.total_card_le θ ν
  have hdimR:((Fintype.card (Aux θ ν)+Fintype.card (Con θ ν):ℕ):ℝ)≤
      2+9*(2:ℝ)^θ+6*((∑l∈Icc 1 θ,2^(θ-l)*ν l:ℕ):ℝ):=by exact_mod_cast hdim
  have hL:(1/2:ℝ)≤Real.log (2/ε):=by
    have hbase:(2:ℝ)≤2/ε:=(le_div_iff₀ he0).mpr (by linarith)
    have hh:=Real.log_le_log (by norm_num : (0:ℝ)<2) hbase
    have hlog:=Real.log_two_gt_d9
    linarith
  have hN:(1:ℝ)≤(2:ℝ)^θ:=one_le_pow₀ (by norm_num)
  have hNkR:(2:ℝ)^θ≤2*(k:ℝ):=by exact_mod_cast hNk
  have hNL:(2:ℝ)^θ≤2*(2:ℝ)^θ*Real.log (2/ε):=by
    have hh:=mul_le_mul_of_nonneg_left hL (show 0≤(2:ℝ)^θ by positivity)
    nlinarith
  have hW':((∑l∈Icc 1 θ,2^(θ-l)*ν l:ℕ):ℝ)≤C*(2:ℝ)^θ*Real.log (2/ε):=hW
  have hsize:((Fintype.card (Aux θ ν)+Fintype.card (Con θ ν):ℕ):ℝ)≤
      (22+6*C)*(2:ℝ)^θ*Real.log (2/ε):=by nlinarith
  have hh:=mul_le_mul_of_nonneg_right hNkR (show 0≤(22+6*C)*Real.log (2/ε) by positivity)
  nlinarith

end SOCMain

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (p q : ℕ) (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
        PolyhedralSOC.Shared.IsPolyhedralApprox k p q ε P ∧ ((p + q : ℕ) : ℝ) ≤ C * k * Real.log (2 / ε) :=
  SOCMain.upper_bound
