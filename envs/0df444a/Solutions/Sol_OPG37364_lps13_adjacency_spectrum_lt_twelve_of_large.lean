-- Prove2me | solution 1 for OPG37364.lps13_adjacency_spectrum_lt_twelve_of_large
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T09:05:22.964864+00:00
-- url     : https://prove2.me/submissions/620559f8-7dbc-41a7-9aa8-b48d739ccae0

/- Fixed-p=13 weak LPS adjacency spectrum bound. Classical DSV-style trace argument; no mathematical novelty claimed. Reuses the proved arithmetic trace estimate and the proved PSL2 eigenspace multiplicity theorem. No connectedness or CFSG assumptions. -/
import Definitions.Def_opg37364_lps13_eigenspaces
import Definitions.Def_opg37364_lps13_trace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Theorems.Thm_OPG37364_lps13_eigenspace_finrank_lower_bound
import Theorems.Thm_OPG37364_lps13_squared_trace_pow_ten_upper_of_scale

noncomputable section Stage18Source0
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Polynomial Matrix

namespace OPG37364.SpectralTrace

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem complex_eigenspace_nontrivial (A : Matrix n n ℝ) (μ : ℝ)
    (hμ : μ ∈ spectrum ℝ A) :
    Nontrivial (Module.End.eigenspace ((A.map (algebraMap ℝ ℂ)).mulVecLin) (μ : ℂ)) := by
  apply Submodule.nontrivial_iff_ne_bot.mpr
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
  rw [Matrix.charpoly_mulVecLin]
  have hr := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
  rw [Matrix.charpoly_map]
  exact (Polynomial.isRoot_map_iff Complex.ofReal_injective).mpr hr

theorem complex_finrank_le_rootMultiplicity (A : Matrix n n ℝ) (μ : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace ((A.map (algebraMap ℝ ℂ)).mulVecLin) (μ : ℂ)) ≤
      A.charpoly.rootMultiplicity μ := by
  have h := LinearMap.finrank_eigenspace_le (A.map (algebraMap ℝ ℂ)).mulVecLin (μ : ℂ)
  rw [Matrix.charpoly_mulVecLin,Matrix.charpoly_map] at h
  have he := Polynomial.eq_rootMultiplicity_map (f := algebraMap ℝ ℂ)
    (p := A.charpoly) Complex.ofReal_injective μ
  have he' : (A.charpoly.map (algebraMap ℝ ℂ)).rootMultiplicity (μ : ℂ) =
      A.charpoly.rootMultiplicity μ := by
    convert he.symm using 1
    simp
  exact h.trans_eq he'

theorem rootMultiplicity_eq_count (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    A.charpoly.rootMultiplicity μ = (Finset.univ.filter fun j => hA.eigenvalues j=μ).card := by
  rw [←Polynomial.count_roots,hA.roots_charpoly_eq_eigenvalues]
  simp [Multiset.count_map,Multiset.countP_eq_card_filter,←Finset.filter_val,eq_comm]

theorem aeval_diagonal_real (d : n → ℝ) (p : Polynomial ℝ) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal (fun j => p.eval (d j)) := by
  change aeval ((Matrix.diagonalAlgHom (n := n) ℝ) d) p = _
  rw [Polynomial.aeval_algHom_apply]
  change Matrix.diagonal (aeval d p)=Matrix.diagonal (fun j => p.eval (d j))
  congr 1
  funext j
  simp [Polynomial.aeval_def,Polynomial.eval₂_at_apply]

theorem trace_conjugate (U : Matrix.unitaryGroup n ℝ) (M : Matrix n n ℝ) :
    Matrix.trace (Unitary.conjStarAlgAut ℝ _ U M)=Matrix.trace M := by
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_comm,←mul_assoc]
  simp

theorem polynomial_squared_trace (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : Polynomial ℝ) :
    Matrix.trace ((aeval A p)^2)=∑ j, (p.eval (hA.eigenvalues j))^2 := by
  have hp : aeval A p = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun j => p.eval (hA.eigenvalues j))) := by
    conv_lhs => rw [hA.spectral_theorem,Polynomial.aeval_algHom_apply]
    congr 1
    simpa using aeval_diagonal_real hA.eigenvalues p
  rw [hp,←map_pow,trace_conjugate]
  simp [Matrix.diagonal_pow,Matrix.trace_diagonal]

theorem eigenvalue_trace_lower (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (μ : ℝ) (p : Polynomial ℝ) :
    (Module.finrank ℂ (Module.End.eigenspace ((A.map (algebraMap ℝ ℂ)).mulVecLin) (μ : ℂ)) : ℝ)*
        (p.eval μ)^2 ≤ Matrix.trace ((aeval A p)^2) := by
  have hd := complex_finrank_le_rootMultiplicity A μ
  rw [rootMultiplicity_eq_count A hA μ] at hd
  rw [polynomial_squared_trace A hA p]
  calc
    (Module.finrank ℂ (Module.End.eigenspace ((A.map (algebraMap ℝ ℂ)).mulVecLin) (μ : ℂ)) : ℝ)*(p.eval μ)^2 ≤
        ((Finset.univ.filter fun j => hA.eigenvalues j=μ).card : ℝ)*(p.eval μ)^2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (sq_nonneg _)
    _ = ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j=μ),
        (p.eval (hA.eigenvalues j))^2 := by
      symm
      calc
        ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j=μ), (p.eval (hA.eigenvalues j))^2 =
            ∑ _j ∈ Finset.univ.filter (fun j => hA.eigenvalues j=μ), (p.eval μ)^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
        _ = _ := by simp
    _ ≤ ∑ j, (p.eval (hA.eigenvalues j))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)

end OPG37364.SpectralTrace

namespace OPG37364

theorem lps13_eigenspace_nontrivial_of_mem_real_spectrum
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (μ : ℝ)
    (hμ : μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ)) :
    Nontrivial (lps13AdjacencyEigenspace hq i μ) := by
  unfold lps13AdjacencyEigenspace lps13AdjacencyEnd
  rw [lps13AdjMatrix_complex]
  exact SpectralTrace.complex_eigenspace_nontrivial _ μ hμ

theorem lps13_eigenspace_trace_lower
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (μ : ℝ) (p : Polynomial ℝ) :
    (Module.finrank ℂ (lps13AdjacencyEigenspace hq i μ) : ℝ)*(p.eval μ)^2 ≤
      Matrix.trace ((aeval ((lps13Graph hq i).adjMatrix ℝ) p)^2) := by
  unfold lps13AdjacencyEigenspace lps13AdjacencyEnd
  rw [lps13AdjMatrix_complex]
  exact SpectralTrace.eigenvalue_trace_lower _
    (Matrix.isHermitian_iff_isSymm.mpr (SimpleGraph.isSymm_adjMatrix _)) μ p

end OPG37364


end

end Stage18Source0

noncomputable section Stage18Source1
set_option autoImplicit false
noncomputable section

namespace OPG37364.PolynomialGrowth

theorem P_zero : lps13NonbacktrackingPolynomial 0 = 1 := rfl
theorem P_one : lps13NonbacktrackingPolynomial 1 = Polynomial.X := rfl
theorem P_rec (n : ℕ) : lps13NonbacktrackingPolynomial (n+2) =
    Polynomial.X * lps13NonbacktrackingPolynomial (n+1) -
      13 * lps13NonbacktrackingPolynomial n := rfl

def scaled (x : ℝ) (m : ℕ) : ℝ :=
  4^m*(lps13NonbacktrackingPolynomial m).eval x

theorem scaled_zero (x : ℝ) : scaled x 0=1 := by
  simp [scaled,P_zero]

theorem scaled_one (x : ℝ) : scaled x 1=4*x := by
  simp [scaled,P_one]

theorem scaled_rec (x : ℝ) (m : ℕ) :
    scaled x (m+2)=4*x*scaled x (m+1)-208*scaled x m := by
  simp only [scaled,P_rec,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat,pow_succ]
  ring

theorem scaled_ratio (x : ℝ) (hx : 12 ≤ x) (m : ℕ) :
    0 ≤ scaled x m ∧ 43*scaled x m ≤ scaled x (m+1) := by
  induction m with
  | zero => simp only [Nat.zero_add,scaled_zero,scaled_one]; constructor <;> linarith
  | succ m ih =>
    have hn : 0 ≤ scaled x (m+1) := by linarith [ih.1,ih.2]
    constructor
    · exact hn
    · rw [show m+1+1=m+2 by omega,scaled_rec]
      have hprod := mul_nonneg (sub_nonneg.mpr hx) hn
      nlinarith [ih.1,ih.2]

theorem scaled_lower (x : ℝ) (hx : 12 ≤ x) (m : ℕ) : 43^m ≤ scaled x m := by
  induction m with
  | zero => simp [scaled_zero]
  | succ m ih =>
    calc
      (43 : ℝ)^(m+1)=43*43^m := pow_succ' _ _
      _ ≤ 43*scaled x m := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ scaled x (m+1) := (scaled_ratio x hx m).2

theorem polynomial_lower (x : ℝ) (hx : 12 ≤ x) (m : ℕ) :
    ((43 : ℝ)/4)^m ≤ (lps13NonbacktrackingPolynomial m).eval x := by
  rw [div_pow]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<4^m)).mpr
  simpa [scaled,mul_comm] using scaled_lower x hx m

theorem exact_growth_check : (2 : ℕ)*4^50*13^46 < 43^50 := by norm_num

end OPG37364.PolynomialGrowth

end

end Stage18Source1

noncomputable section Stage18Source2
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace OPG37364.WeakSpectrum

theorem eventually_polynomial_lt_pow_two (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → C*(5*k+1)^20 < (2 : ℝ)^k := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 20
    (by norm_num : (1 : ℝ)<2)).const_mul (C*6^20)
  have he : ∀ᶠ k : ℕ in atTop, (C*6^20)*((k : ℝ)^20/2^k) < 1 :=
    (tendsto_order.mp ht).2 1 (by simp)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp he
  refine ⟨max K 1,?_⟩
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hfrac := hK k (by omega)
  have hmain : (C*6^20)*(k : ℝ)^20 < 2^k := by
    have hh : ((C*6^20)*(k : ℝ)^20)/2^k < 1 := by
      simpa only [mul_div_assoc] using hfrac
    simpa only [one_mul] using (div_lt_iff₀ (by positivity : (0 : ℝ)<2^k)).mp hh
  calc
    C*(5*k+1)^20 ≤ C*(6*k)^20 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) 20) hC
    _ = (C*6^20)*(k : ℝ)^20 := by ring
    _ < 2^k := hmain

def alpha : ℝ := 43/4

theorem alpha_base : (2 : ℝ)*13^92 ≤ alpha^100 := by norm_num [alpha]

theorem trace_lower_scaled
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ)
    (hμ : μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ))
    (hne : μ ≠ 14) (hbig : 12 ≤ μ) (k : ℕ) :
    (q : ℝ)*alpha^(10*k) ≤
      4*Matrix.trace ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
        (lps13NonbacktrackingPolynomial (5*k)))^2) := by
  have hE := lps13_eigenspace_nontrivial_of_mem_real_spectrum hq i μ hμ
  have hdim := lps13_eigenspace_finrank_lower_bound hq i hnr μ hne (by linarith) hE
  let d := Module.finrank ℂ (lps13AdjacencyEigenspace hq i μ)
  have hd : (q : ℝ)-1 ≤ 2*d := by
    have hh : ((q-1 : ℕ) : ℝ) ≤ 2*d := by exact_mod_cast hdim
    simpa only [Nat.cast_sub (show 1 ≤ q by omega),Nat.cast_one] using hh
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hqd : (q : ℝ) ≤ 4*d := by linarith
  have hg := PolynomialGrowth.polynomial_lower μ hbig (5*k)
  have hsq : alpha^(10*k) ≤ ((lps13NonbacktrackingPolynomial (5*k)).eval μ)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (43/4)^(5*k)) hg 2
    simpa only [alpha,←pow_mul,show 5*k*2=10*k by omega] using hh
  have htrace := lps13_eigenspace_trace_lower hq i μ (lps13NonbacktrackingPolynomial (5*k))
  calc
    (q : ℝ)*alpha^(10*k) ≤ (4*d)*alpha^(10*k) :=
      mul_le_mul_of_nonneg_right hqd (by dsimp [alpha]; positivity)
    _ = 4*((d : ℝ)*alpha^(10*k)) := by ring
    _ ≤ 4*((d : ℝ)*((lps13NonbacktrackingPolynomial (5*k)).eval μ)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left htrace (by norm_num)

theorem contradiction_of_scale (D : ℕ) (hD : 0 < D)
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ)
    (hμ : μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ))
    (hne : μ ≠ 14) (hbig : 12 ≤ μ) (k : ℕ)
    (hlo : 13^(2*k) ≤ q)
    (hu : (Matrix.trace ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
      (lps13NonbacktrackingPolynomial (5*k)))^2))^10 ≤
        (D : ℝ)*(5*k+1)^20*13^(112*k+68))
    (hpoly : (4^10*(D : ℝ)*13^68)*(5*k+1)^20 < (2 : ℝ)^k) : False := by
  let T := Matrix.trace ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
    (lps13NonbacktrackingPolynomial (5*k)))^2)
  have hl := trace_lower_scaled hq i hnr μ hμ hne hbig k
  have hten : (q : ℝ)^10*alpha^(100*k) ≤ 4^10*T^10 := by
    have hh := pow_le_pow_left₀ (by dsimp [alpha]; positivity : 0 ≤ (q : ℝ)*alpha^(10*k)) hl 10
    simpa only [mul_pow,←pow_mul,show 10*k*10=100*k by omega] using hh
  have hqpow : (13 : ℝ)^(20*k) ≤ (q : ℝ)^10 := by
    have hh := Nat.pow_le_pow_left hlo 10
    have hnat : 13^(20*k) ≤ q^10 := by
      convert hh using 1 <;> rw [←pow_mul] <;> congr 1 <;> omega
    exact_mod_cast hnat
  have hapow : (2 : ℝ)^k*13^(92*k) ≤ alpha^(100*k) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*13^92) alpha_base k
    simpa [mul_pow,←pow_mul] using hh
  have hfinal : (2 : ℝ)^k*13^(112*k) ≤
      (4^10*(D : ℝ)*13^68)*(5*k+1)^20*13^(112*k) := by
    calc
      (2 : ℝ)^k*13^(112*k) = 13^(20*k)*(2^k*13^(92*k)) := by
        rw [←mul_assoc,mul_comm (13^(20*k)),mul_assoc,←pow_add]
        congr 2 <;> omega
      _ ≤ (q : ℝ)^10*alpha^(100*k) :=
        mul_le_mul hqpow hapow (by positivity) (by positivity)
      _ ≤ 4^10*T^10 := hten
      _ ≤ 4^10*((D : ℝ)*(5*k+1)^20*13^(112*k+68)) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = (4^10*(D : ℝ)*13^68)*(5*k+1)^20*13^(112*k) := by rw [pow_add]; ring
  have hcancel := (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ)<13^(112*k))).mp hfinal
  exact (not_lt_of_ge hcancel) hpoly

end OPG37364.WeakSpectrum

namespace OPG37364

/-- A weak one-sided adjacency bound for all sufficiently large admissible primes.
The graph is the existing fixed-13 PGL graph, with any chosen square root of -1. -/
theorem _root_.solution :
    ∃ B : ℕ, ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q), B < q →
      ∀ i : LPS13Root q, legendreSym q 13 = -1 → ∀ μ : ℝ,
        μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ) → μ ≠ 14 → μ < 12 := by
  obtain ⟨D,hD,hupper⟩ := lps13_squared_trace_pow_ten_upper_of_scale
  obtain ⟨K,hK⟩ := WeakSpectrum.eventually_polynomial_lt_pow_two
    (4^10*(D : ℝ)*13^68) (by positivity)
  refine ⟨max 13 (169^K),?_⟩
  intro q hp hq hB i hnr μ hμ hne
  let k := Nat.log 169 q
  have hKk : K ≤ k := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hlo : 13^(2*k) ≤ q := by
    have hh := Nat.pow_log_le_self 169 (by omega : q ≠ 0)
    change 169^k ≤ q at hh
    have he : 13^(2*k)=169^k := by rw [pow_mul]; norm_num
    rwa [he]
  have hhi : q < 13^(2*k+2) := by
    have hh : q < 169^(k+1) := Nat.lt_pow_of_log_lt (by norm_num) (by dsimp [k]; omega)
    convert hh using 1 <;> rw [show 169=13^2 by norm_num,←pow_mul] <;> congr 1 <;> omega
  by_contra hbig
  exact WeakSpectrum.contradiction_of_scale D hD hq i hnr μ hμ hne
    (by linarith) k hlo (hupper hq i k hlo hhi) (hK k hKk)

end OPG37364

end

end Stage18Source2
