-- Prove2me | solution 1 for SX.eq_zero_of_expSum_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T12:30:43.764241+00:00
-- url     : https://prove2.me/submissions/b95d3c48-95b1-498e-90be-edc6e1043603

import Definitions.Def_SX

open Complex

namespace ZeroAux

variable {d l : ℕ}

/-- The character attached to a multi-index: `m ↦ exp (⟨λ,x⟩ * ⟨m,y⟩)`, a monoid
homomorphism out of `ℕ^l` written multiplicatively. -/
noncomputable def chi (x : Fin d → ℂ) (y : Fin l → ℂ) (lam : Fin d → ℕ) :
    Multiplicative (Fin l → ℕ) →* ℂ where
  toFun m := Complex.exp (SX.expExponent x lam * SX.latticeSum y (Multiplicative.toAdd m))
  map_one' := by
    show Complex.exp (SX.expExponent x lam * SX.latticeSum y 0) = 1
    simp [SX.latticeSum]
  map_mul' a b := by
    have hadd : SX.latticeSum y (Multiplicative.toAdd a + Multiplicative.toAdd b)
        = SX.latticeSum y (Multiplicative.toAdd a) + SX.latticeSum y (Multiplicative.toAdd b) := by
      simp only [SX.latticeSum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply]
      push_cast; ring
    show Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [show Multiplicative.toAdd (a * b)
          = Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
      hadd, mul_add, Complex.exp_add]

end ZeroAux

open ZeroAux in
theorem solution
    {d l : ℕ} (hl : 2 ≤ l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (L : ℕ) (p : (Fin d → ℕ) → ℤ)
    (h : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0) :
    ∀ lam ∈ SX.box d L, p lam = 0 := by
  classical
  -- `λ ↦ χ_λ` is injective; this is where `hx`, `hy` and `2 ≤ l` are spent
  have hinj : Function.Injective (chi x y (l := l)) := by
    intro lam mu hEq
    -- evaluating at the unit vectors: `(A - B) * y j ∈ 2πi ℤ`
    have hval : ∀ j : Fin l, ∃ n : ℤ,
        (SX.expExponent x lam - SX.expExponent x mu) * y j
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      intro j
      have hls : SX.latticeSum y
          (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single j (1 : ℕ)))) = y j := by
        show SX.latticeSum y (Pi.single j (1 : ℕ)) = y j
        rw [SX.latticeSum, Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ j) hb
      have hpt := DFunLike.congr_fun hEq (Multiplicative.ofAdd (Pi.single j (1 : ℕ)))
      simp only [chi, MonoidHom.coe_mk, OneHom.coe_mk, hls] at hpt
      have h1 : Complex.exp ((SX.expExponent x lam - SX.expExponent x mu) * y j) = 1 := by
        rw [sub_mul, Complex.exp_sub, hpt, div_self (Complex.exp_ne_zero _)]
      exact Complex.exp_eq_one_iff.mp h1
    by_cases hAB : SX.expExponent x lam - SX.expExponent x mu = 0
    · -- `⟨λ - μ, x⟩ = 0`, so `λ = μ` by `ℚ`-linear independence of `x`
      have hAB0 : ∑ i, (lam i : ℂ) * x i = ∑ i, (mu i : ℂ) * x i := by
        simpa [SX.expExponent] using sub_eq_zero.mp hAB
      have key : ∑ i, (((lam i : ℚ) - (mu i : ℚ))) • x i = (0 : ℂ) := by
        have e : ∀ i : Fin d, (((lam i : ℚ) - (mu i : ℚ))) • x i
            = (lam i : ℂ) * x i - (mu i : ℂ) * x i := by
          intro i; rw [Rat.smul_def]; push_cast; ring
        simp only [e, Finset.sum_sub_distrib, hAB0, sub_self]
      have hz := (Fintype.linearIndependent_iff.mp hx) (fun i => (lam i : ℚ) - (mu i : ℚ)) key
      funext i
      have : (lam i : ℚ) = (mu i : ℚ) := sub_eq_zero.mp (hz i)
      exact_mod_cast this
    · exfalso
      have hi0 : (0 : ℕ) < l := by omega
      have hi1 : (1 : ℕ) < l := by omega
      set i0 : Fin l := ⟨0, hi0⟩ with hi0def
      set i1 : Fin l := ⟨1, hi1⟩ with hi1def
      have hne : i0 ≠ i1 := by simp [hi0def, hi1def, Fin.ext_iff]
      obtain ⟨n0, hn0⟩ := hval i0
      obtain ⟨n1, hn1⟩ := hval i1
      have hcomb : (n1 : ℂ) * y i0 - (n0 : ℂ) * y i1 = 0 := by
        have hw : (SX.expExponent x lam - SX.expExponent x mu)
            * ((n1 : ℂ) * y i0 - (n0 : ℂ) * y i1) = 0 := by
          have hr : (SX.expExponent x lam - SX.expExponent x mu)
              * ((n1 : ℂ) * y i0 - (n0 : ℂ) * y i1)
              = (n1 : ℂ) * ((SX.expExponent x lam - SX.expExponent x mu) * y i0)
                - (n0 : ℂ) * ((SX.expExponent x lam - SX.expExponent x mu) * y i1) := by ring
          rw [hr, hn0, hn1]; ring
        rcases mul_eq_zero.mp hw with h1 | h1
        · exact absurd h1 hAB
        · exact h1
      set g : Fin l → ℚ :=
        fun j => if j = i0 then (n1 : ℚ) else if j = i1 then -(n0 : ℚ) else 0 with hgdef
      have hsum : ∑ j, g j • y j = (0 : ℂ) := by
        rw [← Finset.sum_subset (Finset.subset_univ ({i0, i1} : Finset (Fin l)))]
        · rw [Finset.sum_pair hne]
          simp only [hgdef, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
          rw [Rat.smul_def, Rat.smul_def]
          push_cast
          linear_combination hcomb
        · intro j _ hj
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
          simp [hgdef, hj.1, hj.2]
      have hg := (Fintype.linearIndependent_iff.mp hy) g hsum
      have hn0z : n0 = 0 := by
        have := hg i1
        simp only [hgdef, if_neg (Ne.symm hne), if_pos rfl] at this
        exact_mod_cast neg_eq_zero.mp this
      have hy0 : y i0 = 0 := by
        have : (SX.expExponent x lam - SX.expExponent x mu) * y i0 = 0 := by
          rw [hn0, hn0z]; simp
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hAB
        · exact h1
      exact hy.ne_zero i0 hy0
  -- Dedekind independence of characters, transported along the injection
  have hli : LinearIndependent ℂ (fun lam : Fin d → ℕ => ⇑(chi x y lam)) :=
    (linearIndependent_monoidHom (Multiplicative (Fin l → ℕ)) ℂ).comp _ hinj
  have hzero : ∑ lam ∈ SX.box d L, ((p lam : ℂ)) • (⇑(chi x y lam)) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, chi,
      MonoidHom.coe_mk, OneHom.coe_mk]
    exact h (Multiplicative.toAdd m)
  intro lam hlam
  have := linearIndependent_iff'.mp hli (SX.box d L) (fun lam => (p lam : ℂ)) hzero lam hlam
  exact_mod_cast this
