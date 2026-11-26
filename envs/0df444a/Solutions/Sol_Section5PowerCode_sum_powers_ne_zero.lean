-- Prove2me | solution 1 for Section5PowerCode.sum_powers_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:31.875902+00:00
-- url     : https://prove2.me/submissions/52944d96-6b9c-4b76-8ee1-5500699eaac9

import Mathlib
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
theorem solution {F : Type*} [Field F] {m k : ℕ}
    (hm : 0 < m) (hk : m ≤ k) (v : Fin m → F) (hv : Function.Injective v) :
    ∃ j : Fin k, (∑ i, v i ^ (j : ℕ)) ≠ 0 := by
  by_contra h
  push Not at h
  have hmul : Matrix.vecMul (fun _ : Fin m => (1 : F)) (Matrix.vandermonde v)=0 := by
    funext j
    simpa [Matrix.vecMul,dotProduct,Matrix.vandermonde_apply] using h (j.castLE hk)
  have hz := Matrix.eq_zero_of_vecMul_eq_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hv) hmul
  have he := congrFun hz (⟨0,hm⟩ : Fin m)
  exact one_ne_zero he
