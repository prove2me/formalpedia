-- Prove2me | solution 1 for P2M_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one__544717a48388
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:35.961691+00:00
-- url     : https://prove2.me/submissions/2d925016-872f-4850-9b3b-a538b095607b

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_norm_sq_eq_one
import Theorems.Thm_BooleanFun_BV_eq_character_of_eq_sum_degree_one
import Theorems.Thm_BooleanFun_eq_sum_degree_one_of_fourier_weight_one


set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (hn : n>0)
    (hf : fourierWeight 1 f = 1):
    ∃ S ∈ {S|S.card = 1}, ∃ c : ℝ, f = c•χ S := by
  have hf' : ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val := by
    apply eq_sum_degree_one_of_fourier_weight_one
    rw [hf, norm_sq_eq_one hbv]
  exact eq_character_of_eq_sum_degree_one hbv hn hf'
end BooleanFun.BV
