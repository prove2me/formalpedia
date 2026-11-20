-- Prove2me | solution 1 for P010.corePath_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:55:56.099813+00:00
-- url     : https://prove2.me/submissions/32baf3ee-452c-4f49-a056-4c37a5754212

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_classConcat_nodup
public import Theorems.Thm_P010_corePath_perm_classConcat

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hn : 12 ≤ n) :
    (corePath n).Nodup := by
  have hd : (classConcat n (n / 3).primesLE.toList).Nodup :=
    classConcat_nodup n _ (Finset.nodup_toList _)
  exact (corePath_perm_classConcat n hn).nodup_iff.mpr hd
end P010
