-- Prove2me | solution 1 for RiemannMasullo.ratAdeleFundamentalDomain_unique_translate
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:53:26.437204+00:00
-- url     : https://prove2.me/submissions/b0c61b8a-0cf1-484a-9686-10f1cb4a2ee1

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L99-L101
import Mathlib
import Theorems.Thm_RiemannMasullo_exists_sub_diagonal_mem_integralAdeles
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
import Definitions.Def_RiemannMasullo_RationalAdeleFundamentalDomain
open NumberField InfinitePlace.Completion RiemannMasullo IsDedekindDomain
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing Pointwise

theorem solution (a : 𝔸[ℚ]) :
    ∃! q : ℚ, a ∈ algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain := by
  let d := algebraMap ℚ 𝔸[ℚ]
  let R : 𝔸[ℚ] →+* ℝ := (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).comp
    ((Pi.evalRingHom (fun v : InfinitePlace ℚ ↦ v.Completion) Rat.infinitePlace).comp
      (RingHom.fst (InfiniteAdeleRing ℚ) 𝔸ᶠ[𝓞 ℚ, ℚ]))
  have hR (q : ℚ) : R (d q) = (q : ℝ) := by
    change (R.comp d) q = _
    exact eq_ratCast (R.comp d) q
  let I := integralAdelesOutside ℚ ∅
  have hint (q : ℚ) : d q ∈ I ↔ ∃ n : ℤ, (n : ℚ) = q := by
    rw [show (d q ∈ I) ↔ _ from diagonal_mem_integralAdelesOutside ℚ ∅ q]
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨_, Rat.ringOfIntegersEquiv_apply_coe r⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, Rat.ringOfIntegersEquiv_symm_apply_coe n⟩
  have hmem (q : ℚ) : a ∈ d q +ᵥ ratAdeleFundamentalDomain ↔
      R (a - d q) ∈ Set.Ico 0 1 ∧ a - d q ∈ I := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [vadd_eq_add, add_sub_cancel_left]
      exact hy
    · intro hy
      exact ⟨a - d q, hy, by change d q + (a - d q) = a; abel⟩
  obtain ⟨r, hr⟩ := exists_sub_diagonal_mem_integralAdeles ℚ a
  let t := R (a - d r)
  let n := ⌊t⌋
  let q := r + (n : ℚ)
  have hqeq : a - d q = (a - d r) - d (n : ℚ) := by dsimp [q]; rw [map_add]; abel
  have hq : R (a - d q) ∈ Set.Ico 0 1 ∧ a - d q ∈ I := by
    rw [hqeq]
    refine ⟨?_, I.sub_mem hr ((hint _).mpr ⟨n, rfl⟩)⟩
    rw [map_sub, hR, Rat.cast_intCast]
    exact ⟨sub_nonneg.mpr (Int.floor_le t), by linarith [Int.lt_floor_add_one t]⟩
  refine ⟨q, (hmem q).mpr hq, ?_⟩
  intro p hp
  obtain ⟨hpR, hpI⟩ := (hmem p).mp hp
  have hpq : d (p - q) ∈ I := by
    rw [map_sub, show d p - d q = (a - d q) - (a - d p) by abel]
    exact I.sub_mem hq.2 hpI
  obtain ⟨k, hk⟩ := (hint _).mp hpq
  have hkr : (k : ℝ) = R (a - d q) - R (a - d p) := by
    rw [map_sub, map_sub, hR, hR]
    have h' : (k : ℝ) = (p : ℝ) - (q : ℝ) := by exact_mod_cast hk
    linarith
  obtain ⟨hp0, hp1⟩ := hpR
  obtain ⟨hq0, hq1⟩ := hq.1
  have hlow : (-1 : ℝ) < k := by linarith
  have hhigh : (k : ℝ) < 1 := by linarith
  have hl : (-1 : ℤ) < k := by exact_mod_cast hlow
  have hu : k < 1 := by exact_mod_cast hhigh
  have : k = 0 := by omega
  exact sub_eq_zero.mp (by simpa [this] using hk.symm)
