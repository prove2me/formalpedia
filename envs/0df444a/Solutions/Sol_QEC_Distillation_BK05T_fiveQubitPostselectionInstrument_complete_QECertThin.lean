-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitPostselectionInstrument_complete_QECertThin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:06:35.513774+00:00
-- url     : https://prove2.me/submissions/c59d052b-b75a-4738-b379-c028c94dbdd0

import Definitions.Def_QECert_BK05T_InstrumentThin
open QEC.Coding.PauliSymplectic
open QEC.Distillation.BK05T

theorem solution :
    (jointStabilizerKrausFamily fiveQubitCheck_QECertInstrumentThin fiveQubitChecks_commute_QECertInstrumentThin).Complete := by
  exact jointStabilizerKrausFamily_complete fiveQubitCheck_QECertInstrumentThin fiveQubitChecks_commute_QECertInstrumentThin
