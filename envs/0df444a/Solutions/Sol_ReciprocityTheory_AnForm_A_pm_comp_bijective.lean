-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_comp_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:55.841304+00:00
-- url     : https://prove2.me/submissions/c55557b8-272c-42c9-af16-b74d298817a2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (τ : Equiv.Perm (Fin D)) :
    Function.Bijective (fun g : Fin D → Fin D × ι => g ∘ τ) :=
  ⟨fun g h e => by funext a; simpa using congrFun e (τ.symm a),
    fun g => ⟨g ∘ τ.symm, by funext a; simp⟩⟩
end ReciprocityTheory.AnForm.A
