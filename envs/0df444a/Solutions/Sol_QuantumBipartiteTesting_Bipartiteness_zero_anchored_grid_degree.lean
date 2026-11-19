-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.zero_anchored_grid_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:56:11.883028+00:00
-- url     : https://prove2.me/submissions/28fab4a3-4026-40b7-a51d-717d9ce9fe95

-- Endpoint argument adapted from formalcs/circuit-complexity, release/0.2.0,
-- Apache 2.0; attribution and license in ReferenceSources/circuit-complexity.
-- This variant uses the additional zero boundary value of the gap polynomial.
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_interior_integer_grid_bound
import Theorems.Thm_markov_inequality_interval

namespace QuantumBipartiteTesting.Bipartiteness
noncomputable section
open Finset Polynomial
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

private def SectionPoly (Q : Bivariate) (a b : ℝ[X]) : ℝ[X] := Q.eval₂ Polynomial.C ![a,b]

private lemma section_degree (Q : Bivariate) (a b : ℝ[X])
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    (SectionPoly Q a b).natDegree ≤ Q.totalDegree := by
  unfold SectionPoly
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply le_trans (Polynomial.natDegree_mul_le)
  simp only [Polynomial.natDegree_C,zero_add]
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  apply le_trans (Finset.sum_le_sum (fun i hi => ?_)) (MvPolynomial.le_totalDegree hd)
  apply le_trans (Polynomial.natDegree_pow_le)
  have h : (![a,b] i).natDegree ≤ 1 := by fin_cases i <;> assumption
  simpa using Nat.mul_le_mul_left (d i) h

private lemma section_eval (Q : Bivariate) (a b : ℝ[X]) (x : ℝ) :
    (SectionPoly Q a b).eval x = Eval Q (a.eval x) (b.eval x) := by
  change Polynomial.evalRingHom x (Q.eval₂ Polynomial.C ![a,b]) =
    Q.eval₂ (RingHom.id ℝ) ![a.eval x,b.eval x]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    simp
  have hv : (Polynomial.evalRingHom x) ∘ ![a,b] = ![a.eval x,b.eval x] := by
    funext i
    fin_cases i <;> rfl
  rw [hc,hv]

private lemma interval_lipschitz {p : ℝ[X]} {d : ℕ} {N M x y : ℝ}
    (hd : p.natDegree ≤ d) (hN : 0 < N) (hM : 0 < M)
    (hb : ∀ z ∈ Set.Icc 0 N, |p.eval z| ≤ M)
    (hx : x ∈ Set.Icc 0 N) (hy : y ∈ Set.Icc 0 N) :
    |p.eval y-p.eval x| ≤ (2*(d:ℝ)^2*M/N)*|y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun x : ℝ => p.eval x) (fun z _ => p.differentiableAt)
    (C := 2*(d:ℝ)^2*M/N)
    (by intro z hz; simpa only [Polynomial.deriv, Real.norm_eq_abs,sub_zero] using
      markov_inequality_interval 0 N hN p M hd (fun x hx0 hxN => hb x ⟨hx0,hxN⟩) z hz.1 hz.2)
    (convex_Icc 0 N) hx hy
  simpa only [Real.norm_eq_abs] using h

private lemma endpoint_grid_degree {p : ℝ[X]} {n d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hd : p.natDegree ≤ d)
    (hb : ∀ k : ℕ, k ≤ n → |p.eval (k:ℝ)| ≤ 4/3)
    (hgap : γ ≤ |p.eval 1-p.eval 0|) :
    γ*(n:ℝ) ≤ 16*(γ+1)*(d:ℝ)^2 := by
  by_cases hn : n = 0
  · subst n; simp; positivity
  have hN : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h0 : (0:ℝ) ∈ Set.Icc 0 (n:ℝ) := ⟨le_rfl,hN.le⟩
  have h1 : (1:ℝ) ∈ Set.Icc 0 (n:ℝ) := ⟨by norm_num,by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn⟩
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (s := Set.Icc (0:ℝ) n) ⟨0,le_rfl,hN.le⟩ p.continuous.abs.continuousOn
  let M := |p.eval x|
  have hMb : ∀ z ∈ Set.Icc 0 (n:ℝ), |p.eval z| ≤ M := hmax
  have hM : 0 < M := by
    have hh := abs_sub_le (p.eval 1) 0 (p.eval 0)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have ha := hMb 0 h0
    have hb := hMb 1 h1
    linarith
  have hnear : (Nat.floor x:ℝ) ∈ Set.Icc 0 (n:ℝ) :=
    ⟨by positivity,(Nat.floor_le hx.1).trans hx.2⟩
  have hdist : |x-(Nat.floor x:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hx.1))]
    linarith [Nat.lt_floor_add_one x]
  have hnearbound := hb (Nat.floor x) (Nat.floor_le_of_le hx.2)
  have herr := interval_lipschitz hd hN hM hMb hnear hx
  have hcoef : 0 ≤ 2*(d:ℝ)^2*M/n := by positivity
  have hnorm : M ≤ 4/3+2*(d:ℝ)^2*M/n := by
    have ht := abs_sub_le (p.eval x) (p.eval (Nat.floor x:ℝ)) 0
    simp only [sub_zero] at ht
    have hh := mul_le_mul_of_nonneg_left hdist hcoef
    dsimp [M] at *
    nlinarith
  by_cases hlarge : (n:ℝ) ≤ 4*(d:ℝ)^2
  · nlinarith [mul_nonneg hγ.le (sub_nonneg.mpr hlarge),sq_nonneg (d:ℝ)]
  have hMsmall : M ≤ 8/3 := by
    have hh := (le_div_iff₀ hN).mp (show M-4/3 ≤ 2*(d:ℝ)^2*M/n by linarith)
    nlinarith
  have hdiff := interval_lipschitz hd hN hM hMb h0 h1
  norm_num only [sub_zero,abs_one,mul_one] at hdiff
  have hh := (le_div_iff₀ hN).mp (hgap.trans hdiff)
  have hp := mul_le_mul_of_nonneg_left hMsmall (show 0 ≤ 2*(d:ℝ)^2 by positivity)
  nlinarith [mul_nonneg hγ.le (sq_nonneg (d:ℝ))]

private lemma grid_degree (γ : ℝ) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ C R : ℕ, 0 < C → 2 ≤ R → ∀ Q : Bivariate,
      (∀ X l : ℤ, 1 ≤ l → l ≤ (R:ℤ) →
        |(X:ℝ)-C| ≤ (R:ℝ)^(3/2:ℝ)/2 → l ∣ X → |Eval Q X l| ≤ 1) →
      Eval Q C 0 = 0 → γ ≤ |Eval Q C 1| → c*Real.sqrt R ≤ (Q.totalDegree:ℝ) := by
  let c := γ/(1024*(γ+1))
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hceq : 1024*(γ+1)*c = γ := by dsimp [c]; field_simp
  have hcup : c ≤ 1/1024 := by
    dsimp [c]
    apply (div_le_iff₀ (by positivity : 0 < 1024*(γ+1))).mpr
    linarith
  refine ⟨c,hcpos,?_⟩
  intro C R hC hR Q hgrid hzero hgap
  have hRp : 0 < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hrootpos : 0 < Real.sqrt (R:ℝ) := Real.sqrt_pos.mpr hRp
  have hsquare := Real.sq_sqrt hRp.le
  have hdpos : 1 ≤ Q.totalDegree := by
    by_contra hn
    have hd0 : Q.totalDegree = 0 := by omega
    have hQ := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd0
    rw [hQ] at hzero hgap
    simp only [Eval,MvPolynomial.eval_C] at hzero hgap
    rw [hzero,abs_zero] at hgap
    linarith
  by_contra hn
  have hsmall : (Q.totalDegree:ℝ) < c*Real.sqrt R := lt_of_not_ge hn
  have hRlarge : 65536 < (R:ℝ) := by
    by_contra hh
    have hroot : Real.sqrt (R:ℝ) ≤ 256 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
    have hmul := mul_le_mul hcup hroot hrootpos.le (by norm_num : (0:ℝ) ≤ 1/1024)
    have hdp : (1:ℝ) ≤ Q.totalDegree := by exact_mod_cast hdpos
    nlinarith
  have hroot : 256 < Real.sqrt (R:ℝ) := by nlinarith [Real.sqrt_nonneg (R:ℝ)]
  by_cases hcenter : ∀ l : ℤ, 1 ≤ l → l ≤ (R:ℤ) → |Eval Q C l| ≤ 4/3
  · let p := SectionPoly Q (Polynomial.C (C:ℝ)) Polynomial.X
    have hp : p.natDegree ≤ Q.totalDegree := section_degree Q _ _ (by simp) (by compute_degree)
    have heval (x : ℝ) : p.eval x = Eval Q C x := by
      rw [section_eval]; simp
    have hb : ∀ k : ℕ, k ≤ R-1 → |p.eval (k:ℝ)| ≤ 4/3 := by
      intro k hk
      rw [heval]
      by_cases hk0 : k = 0
      · subst k
        simpa only [Nat.cast_zero,hzero,abs_zero] using (by norm_num : (0:ℝ) ≤ 4/3)
      · have hh := hcenter (k:ℤ) (by omega) (by omega)
        simpa only [Int.cast_natCast] using hh
    have hgp : γ ≤ |p.eval 1-p.eval 0| := by simpa only [heval,hzero,sub_zero] using hgap
    have he := endpoint_grid_degree hγ hp hb hgp
    have hR2 : (R:ℝ) ≤ 2*((R-1:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one]
      have hr : (2:ℝ) ≤ R := by exact_mod_cast hR
      linarith
    have hsq : (Q.totalDegree:ℝ)^2 ≤ c^2*(R:ℝ) := by
      have hh := (mul_self_lt_mul_self (Nat.cast_nonneg Q.totalDegree) hsmall).le
      nlinarith
    have hcc := congrArg (fun x : ℝ => x*c) hceq
    have hγc : γ*c ≤ γ := mul_le_of_le_one_right hγ.le (by linarith [hcup])
    have hstrict : 32*(γ+1)*c^2 < γ := by nlinarith
    have hstrictR := mul_lt_mul_of_pos_right hstrict hRp
    have hleR := mul_le_mul_of_nonneg_left hR2 hγ.le
    have hleD := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 32*(γ+1) by positivity)
    nlinarith
  · push Not at hcenter
    obtain ⟨l,hl,hlR,hlgap⟩ := hcenter
    have hlpos : 0 < (l:ℝ) := by exact_mod_cast (show 0 < l by omega)
    have hlone : (1:ℝ) ≤ l := by exact_mod_cast hl
    have hlr : (l:ℝ) ≤ R := by exact_mod_cast hlR
    let m := Nat.floor (Real.sqrt (R:ℝ)/64)
    have hmfloor : (m:ℝ) ≤ Real.sqrt (R:ℝ)/64 := Nat.floor_le (by positivity)
    have hmceil : Real.sqrt (R:ℝ)/64 < (m:ℝ)+1 := Nat.lt_floor_add_one _
    have hmpos : 0 < m := by exact_mod_cast (show (0:ℝ) < m by linarith)
    have hmd : (Q.totalDegree:ℝ) < (m:ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hcup hrootpos.le
      linarith
    have hmdnat : Q.totalDegree < 2*m+2 := by
      have hh : Q.totalDegree < m := by exact_mod_cast hmd
      omega
    let a := Int.floor ((C:ℝ)/(l:ℝ))
    let z := (C:ℝ)/(l:ℝ)-(a:ℝ)
    have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
    have hz1 : z ≤ 1 := (Int.fract_lt_one ((C:ℝ)/(l:ℝ))).le
    let p := SectionPoly Q (Polynomial.C (l:ℝ)*(Polynomial.X+Polynomial.C (a:ℝ))) (Polynomial.C (l:ℝ))
    have hp : p.natDegree < 2*m+2 := (section_degree Q _ _ (by compute_degree) (by simp)).trans_lt hmdnat
    have heval (x : ℝ) : p.eval x = Eval Q ((l:ℝ)*(x+a)) l := by
      rw [section_eval]; simp
    have hpower : (R:ℝ)^(3/2:ℝ) = (R:ℝ)*Real.sqrt R := by
      rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hRp,Real.rpow_one,← Real.sqrt_eq_rpow]
    have hb : ∀ x : ℤ, -(16*(m:ℤ)) ≤ x → x ≤ 16*(m:ℤ)+1 → |p.eval (x:ℝ)| ≤ 1 := by
      intro x hx hx'
      rw [heval]
      have hxl : -(16*(m:ℝ)) ≤ (x:ℝ) := by exact_mod_cast hx
      have hxu : (x:ℝ) ≤ 16*(m:ℝ)+1 := by exact_mod_cast hx'
      have hdist : |(x:ℝ)-z| ≤ 16*(m:ℝ)+1 := by rw [abs_le]; constructor <;> linarith
      have hsize : 16*(m:ℝ)+1 ≤ Real.sqrt (R:ℝ)/2 := by linarith
      have hcd : (l:ℝ)*((x:ℝ)+a)-C = (l:ℝ)*((x:ℝ)-z) := by
        dsimp [z]
        field_simp
        ring
      have hbound : |(l:ℝ)*((x:ℝ)+a)-C| ≤ (R:ℝ)^(3/2:ℝ)/2 := by
        rw [hcd,abs_mul,abs_of_pos hlpos,hpower]
        have hh := mul_le_mul_of_nonneg_left (hdist.trans hsize) hlpos.le
        have hh' := mul_le_mul_of_nonneg_right hlr (show 0 ≤ Real.sqrt (R:ℝ)/2 by positivity)
        nlinarith
      have hh := hgrid (l*(x+a)) l hl hlR (by simpa using hbound) ⟨x+a,rfl⟩
      simpa using hh
    have hez := interior_integer_grid_bound m hmpos p hp hb z hz hz1
    rw [heval] at hez
    have harg : (l:ℝ)*(z+a) = C := by dsimp [z]; field_simp; ring
    rw [harg] at hez
    exact (not_le_of_gt hlgap) hez

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution : ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
    ∀ C R : ℕ, 0 < C → 2 ≤ R → ∀ Q : Bivariate,
      (∀ X l : ℤ, 1 ≤ l → l ≤ (R:ℤ) →
        |(X:ℝ)-C| ≤ (R:ℝ)^(3/2:ℝ)/2 → l ∣ X → |Eval Q X l| ≤ 1) →
      Eval Q C 0 = 0 → γ ≤ |Eval Q C 1| → c*Real.sqrt R ≤ (Q.totalDegree:ℝ) := grid_degree
