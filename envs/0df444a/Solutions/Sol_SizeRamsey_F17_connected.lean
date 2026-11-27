-- Prove2me | solution 1 for SizeRamsey.F17_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:41.631191+00:00
-- url     : https://prove2.me/submissions/534d199a-caa2-4ed5-b36d-9493c61359fd

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution :
    F17.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨5, ?_⟩
  have e : ∀ a b : Fin 12, F17.Adj a b → F17.Reachable a b := fun _ _ h => h.reachable
  have r0 : F17.Reachable 5 0 := e _ _ (by decide)
  have r1 : F17.Reachable 5 1 := e _ _ (by decide)
  have r2 : F17.Reachable 5 2 := e _ _ (by decide)
  have r6 : F17.Reachable 5 6 := e _ _ (by decide)
  have r3 : F17.Reachable 5 3 := r1.trans (e _ _ (by decide))
  have r4 : F17.Reachable 5 4 := r0.trans (e _ _ (by decide))
  have r10 : F17.Reachable 5 10 := r6.trans (e _ _ (by decide))
  have r11 : F17.Reachable 5 11 := r6.trans (e _ _ (by decide))
  have r7 : F17.Reachable 5 7 := r10.trans (e _ _ (by decide))
  have r8 : F17.Reachable 5 8 := r10.trans (e _ _ (by decide))
  have r9 : F17.Reachable 5 9 := r7.trans (e _ _ (by decide))
  intro w
  fin_cases w
  exacts [r0, r1, r2, r3, r4, SimpleGraph.Reachable.refl _, r6, r7, r8, r9, r10, r11]
end SizeRamsey
