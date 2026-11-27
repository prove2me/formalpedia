-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:42.459831+00:00
-- url     : https://prove2.me/submissions/23cc01b7-2e5b-4bb1-97bd-ae130ffe9665

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.B3 ReciprocityTheory.ChartRestriction.B3.IotaPl
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.ChartRestriction.B3.IotaPl
theorem _root_.solution : ‖(p : ℂ_[p])‖ < 1 := by
  have e : (p : ℂ_[p]) = (((algebraMap ℚ_[p] (PadicAlgCl p)) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    first
      | simp
      | (rw [map_natCast]; exact (map_natCast UniformSpace.Completion.coeRingHom p).symm)
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
    | exact Padic.norm_p_lt_one
    | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
    | (rw [padicNormE.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
end ReciprocityTheory.ChartRestriction.B3.IotaPl
